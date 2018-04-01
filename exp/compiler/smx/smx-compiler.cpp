// vim: set ts=2 sw=2 tw=99 et:
// 
// Copyright (C) 2012-2014 David Anderson
// 
// This file is part of SourcePawn.
// 
// SourcePawn is free software: you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option)
// any later version.
// 
// SourcePawn is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License along with
// SourcePawn. If not, see http://www.gnu.org/licenses/.
#include "compile-context.h"
#include "parser/ast.h"
#include "scopes.h"
#include "smx-compiler.h"
#include <amtl/am-algorithm.h>
#include <amtl/am-maybe.h>
#include <smx/smx-v1.h>
#include <sp_vm_types.h>

#define __ masm_.

namespace sp {

static bool HasSimpleCellStorage(Type* type);

typedef SmxListSection<sp_file_natives_t> SmxNativeSection;
typedef SmxListSection<sp_file_publics_t> SmxPublicSection;
typedef SmxListSection<sp_file_pubvars_t> SmxPubvarSection;
typedef SmxBlobSection<sp_file_data_t> SmxDataSection;
typedef SmxBlobSection<sp_file_code_t> SmxCodeSection;

uint64_t SValue::sSequenceNo = 0;

SmxCompiler::SmxCompiler(CompileContext& cc, sema::Program* program)
 : cc_(cc),
   program_(program),
   pri_value_(0),
   alt_value_(0),
   max_var_stk_(0),
   cur_var_stk_(0)
{
  names_ = new SmxNameTable(".names");
  builder_.add(names_);
}

bool
SmxCompiler::compile()
{
  // This is always the first opcode, so instruction 0 is invalid.
  __ opcode(OP_HALT);

  for (ast::VarDecl* decl : program_->globals) {
    if (!cc_.canContinueProcessing())
      return false;

    generateData(decl);
  }

  for (ast::FunctionStatement* fun : program_->functions) {
    if (!cc_.canContinueProcessing())
      return false;

    generate(fun);
  }

  if (masm_.outOfMemory()) {
    cc_.report(SourceLocation(), rmsg::outofmemory);
    return false;
  }

  // :TODO: error
  assert(publics_.length());
  qsort(publics_.buffer(), publics_.length(), sizeof(FunctionEntry), sort_functions);
  if (natives_.length())
    qsort(natives_.buffer(), natives_.length(), sizeof(FunctionEntry), sort_functions);

  assert(masm_.buffer_length() % sizeof(cell_t) == 0);
  assert(data_.size() % sizeof(cell_t) == 0);

  RefPtr<SmxCodeSection> code = new SmxCodeSection(".code");
  code->header().codesize = masm_.buffer_length();
  code->header().cellsize = sizeof(cell_t);
  code->header().codeversion = 12;
  code->header().flags = CODEFLAG_DEBUG;
  code->header().main = 0;
  code->header().code = sizeof(sp_file_code_t);
  code->setBlob(masm_.buffer(), masm_.buffer_length());
  builder_.add(code);

  // Ensure the data section has at least one value.
  // :TODO: clean up data handling, check <= INT_MAX, not overflowed
  if (!data_.size())
    data_.write(0);

  RefPtr<SmxDataSection> data = new SmxDataSection(".data");
  data->header().datasize = data_.size();
  data->header().memsize = data_.size() + 4096; // :TODO: real value
  data->header().data = sizeof(sp_file_data_t);
  data->setBlob(data_.bytes(), data_.size());
  builder_.add(data);

  RefPtr<SmxPublicSection> publics = new SmxPublicSection(".publics");
  for (size_t i = 0; i < publics_.length(); i++) {
    const FunctionEntry& entry = publics_[i];

    sp_file_publics_t& pf = publics->add();
    pf.address = entry.fun->address()->offset();
    pf.name = names_->add(entry.name);
  }
  builder_.add(publics);

  RefPtr<SmxPubvarSection> pubvars = new SmxPubvarSection(".pubvars");
  builder_.add(pubvars);

  RefPtr<SmxNativeSection> natives =  new SmxNativeSection(".natives");
  for (size_t i = 0; i < natives_.length(); i++) {
    const FunctionEntry& entry = natives_[i];

    sp_file_natives_t& nf = natives->add();
    nf.name = names_->add(entry.name);

    __ bind_to(entry.fun->address(), (uint32_t)i);
  }
  builder_.add(natives);

  return cc_.phasePassed();
}

bool
SmxCompiler::emit(ISmxBuffer* buffer)
{
  return builder_.write(buffer);
}

void
SmxCompiler::generate(ast::FunctionStatement* fun)
{
  // :TODO: move this into local state, otherwise nested functions will be hard.
  max_var_stk_ = 0;
  cur_var_stk_ = 0;

  __ bind(fun->address());
  __ opcode(OP_PROC);

  // :TODO: don't generate if no local vars
  __ opcode(OP_STACK, &entry_stack_op_);

  generateBlock(fun->body());

  __ bind_to(&entry_stack_op_, -max_var_stk_);

  if (!fun->guaranteed_return()) {
    __ opcode(OP_ZERO_PRI);
    __ opcode(OP_RETN);
  }
  __ opcode(OP_ENDPROC);

  if (!(fun->attrs() & ast::DeclAttrs::Public)) {
    cc_.report(fun->loc(), rmsg::non_public_not_supported);
    return;
  }

  publics_.append(FunctionEntry(fun->name(), fun));
}

void
SmxCompiler::generateStatement(ast::Statement* stmt)
{
  // :TODO: track stack depth
  switch (stmt->kind()) {
    case ast::AstKind::kReturnStatement:
      generateReturn(stmt->toReturnStatement());
      break;
    case ast::AstKind::kExpressionStatement:
      generateExprStatement(stmt->toExpressionStatement());
      break;
    case ast::AstKind::kVarDecl:
      generateVarDecl(stmt->toVarDecl());
      break;
    default:
      assert(false);
  }

  // If compilation is going okay, the operand stack should be empty.
  if (cc_.phasePassed() &&
      (!operand_stack_.empty() || pri_value_ || alt_value_))
  {
    cc_.report(SourceLocation(), rmsg::regalloc_error) <<
      "operand stack is not empty at end of statement";
  }
}

void
SmxCompiler::generateBlock(ast::BlockStatement* block)
{
  // :TODO: raii this, so for loops can use it for the init scope
  int32_t stk_usage = cur_var_stk_;

  ast::StatementList* statements = block->statements();
  for (size_t i = 0; i < statements->length(); i++) {
    ast::Statement* stmt = statements->at(i);
    generateStatement(stmt);
  }

  // Commit this scope's stack usage to the frame, then drop our local usage.
  max_var_stk_ = ke::Max(max_var_stk_, cur_var_stk_);
  cur_var_stk_ = stk_usage;
}

void
SmxCompiler::generateVarDecl(ast::VarDecl* stmt)
{
  // :TODO: assert not const
  VariableSymbol* sym = stmt->sym();
  int32_t size = compute_storage_size(sym->type());

  switch (sym->scope()->kind()) {
    case Scope::Block:
      if (!ke::IsUint32AddSafe(uint32_t(size), uint32_t(cur_var_stk_))) {
        cc_.report(stmt->loc(), rmsg::too_much_stack);
        return;
      }

      cur_var_stk_ += size;
      sym->allocate(StorageClass::Local, -cur_var_stk_);
      break;

    default:
      cc_.report(stmt->loc(), rmsg::unimpl_kind) <<
        "smx-var-scope" << int32_t(sym->scope()->kind());
      sym->allocate(StorageClass::Local, 0);
      break;
  }

  if (sema::Expr* init = stmt->sema_init()) {
    if (!HasSimpleCellStorage(sym->type())) {
      cc_.report(stmt->loc(), rmsg::unimpl_kind) <<
        "var-decl-init", BuildTypeName(sym->type());
      return;
    }

    store_into(sym, init);
  }
}

void
SmxCompiler::generateExprStatement(ast::ExpressionStatement* stmt)
{
  sema::Expr* expr = stmt->sema_expr();
  emit_into(expr, ValueDest::Pri);
}

void
SmxCompiler::generateReturn(ast::ReturnStatement* stmt)
{
  emit_into(stmt->sema_expr(), ValueDest::Pri);
  __ opcode(OP_RETN);
}

bool
SmxCompiler::emit_into(sema::Expr* expr, ValueDest dest)
{
  ValueDest actual = emit(expr, dest);
  if (actual == ValueDest::Error)
    return false;
  if (actual == dest)
    return true;

  will_kill(dest);
  if (dest == ValueDest::Pri || dest == ValueDest::Alt) {
    // move.pri = pri <- alt
    // move.alt = alt <- pri
    //
    // Since actual != dest, we just need to move into the opposite register.
    if (actual == ValueDest::Alt)
      __ opcode(OP_MOVE_PRI);
    else
      __ opcode(OP_MOVE_ALT);
    return true;
  }

  assert(dest == ValueDest::Stack);
  if (actual == ValueDest::Pri)
    __ opcode(OP_PUSH_PRI);
  else if (actual == ValueDest::Alt)
    __ opcode(OP_PUSH_ALT);
  else
    assert(false);

  return true;
}

ValueDest
SmxCompiler::emit(sema::Expr* expr, ValueDest dest)
{
  switch (expr->kind()) {
  case sema::ExprKind::ConstValue:
    return emitConstValue(expr->toConstValueExpr(), dest);
  case sema::ExprKind::Binary:
    return emitBinary(expr->toBinaryExpr(), dest);
  case sema::ExprKind::Unary:
    return emitUnary(expr->toUnaryExpr(), dest);
  case sema::ExprKind::Call:
    return emitCall(expr->toCallExpr(), dest);
  case sema::ExprKind::Var:
    return emitVar(expr->toVarExpr(), dest);
  case sema::ExprKind::TrivialCast:
    return emitTrivialCast(expr->toTrivialCastExpr(), dest);
  default:
    cc_.report(expr->src()->loc(), rmsg::unimpl_kind) <<
      "smx-emit-expr" << expr->prettyName();
    return ValueDest::Error;
  }
}

ValueDest
SmxCompiler::emitConstValue(sema::ConstValueExpr* expr, ValueDest dest)
{
  cell_t value = 0;
  const BoxedValue& box = expr->value();

  switch (box.kind()) {
  case BoxedValue::Kind::Integer:
  {
    const IntValue& iv = box.toInteger();
    assert(iv.valueFitsInInt32());
    value = (int32_t)iv.asSigned();
    break;
  }
  default:
    assert(false);
  }

  will_kill(dest);

  switch (dest) {
  case ValueDest::Pri:
    __ opcode(OP_CONST_PRI, value);
    break;
  case ValueDest::Alt:
    __ opcode(OP_CONST_ALT, value);
    break;
  case ValueDest::Stack:
    __ opcode(OP_PUSH_C, value);
    break;
  default:
    assert(false);
  }

  return dest;
}

ValueDest
SmxCompiler::emitVar(sema::VarExpr* expr, ValueDest dest)
{
  VariableSymbol* sym = expr->sym();

  assert(sym->type()->isPrimitive());

  switch (sym->storage()) {
    case StorageClass::Argument:
    case StorageClass::Local:
      will_kill(dest);
      if (dest == ValueDest::Pri)
        __ opcode(OP_LOAD_S_PRI, sym->address());
      else if (dest == ValueDest::Alt)
        __ opcode(OP_LOAD_S_ALT, sym->address());
      else if (dest == ValueDest::Stack)
        __ opcode(OP_PUSH_S, sym->address());
      else
        assert(false);
      return dest;

    case StorageClass::Global:
      will_kill(dest);
      if (dest == ValueDest::Pri)
        __ opcode(OP_LOAD_PRI, sym->address());
      else if (dest == ValueDest::Alt)
        __ opcode(OP_LOAD_ALT, sym->address());
      else if (dest == ValueDest::Stack)
        __ opcode(OP_PUSH, sym->address());
      else
        assert(false);
      return dest;

    default:
      cc_.report(expr->src()->loc(), rmsg::unimpl_kind) <<
        "emit-var-sc-kind" << int32_t(sym->storage());
      return ValueDest::Error;
  }
}

static inline ke::Maybe<int32_t>
MaybeConstInt32(sema::Expr* expr)
{
  sema::ConstValueExpr* cv = expr->asConstValueExpr();
  if (!cv)
    return Nothing();

  const BoxedValue& box = cv->value();
  if (box.kind() != BoxedValue::Kind::Integer)
    return Nothing();

  const IntValue& iv = box.toInteger();
  if (!iv.valueFitsInInt32())
    return Nothing();

  return Some((int32_t)iv.asSigned());
}

ValueDest
SmxCompiler::emitBinary(sema::BinaryExpr* expr, ValueDest dest)
{
  sema::Expr* left = expr->left();
  sema::Expr* right = expr->right();

  Maybe<int32_t> left_i32 = MaybeConstInt32(left);
  Maybe<int32_t> right_i32 = MaybeConstInt32(right);

  // Special case SHL since it has a specific optimization and it's gross to
  // fall-through case statements in a complex switch.
  if (expr->token() == TOK_SHL && right_i32) {
    // If we don't have to push to the stack, we can pick exactly which
    // register was requested.
    ValueDest actual = (dest == ValueDest::Stack)
                       ? ValueDest::Pri
                       : dest;
    if (!emit_into(left, actual))
      return ValueDest::Error;

    if (actual == ValueDest::Pri)
      __ opcode(OP_SHL_C_PRI, *right_i32);
    else
      __ opcode(OP_SHL_C_ALT, *right_i32);
    return actual;
  }

  switch (expr->token()) {
    case TOK_PLUS:
    case TOK_STAR:
    case TOK_EQUALS:
    {
      // Try to get left=expr and right=const for commutative operations.
      if (left_i32 && !right_i32 &&
          (expr->token() == TOK_PLUS || expr->token() == TOK_STAR))
      {
        ke::Swap(left, right);
        ke::Swap(left_i32, right_i32);
      }

      if (!emit_into(left, ValueDest::Pri))
        return ValueDest::Error;

      // Use .C variants.
      if (right_i32) {
        if (expr->token() == TOK_PLUS)
          __ opcode(OP_ADD_C, *right_i32);
        else if (expr->token() == TOK_STAR)
          __ opcode(OP_SMUL_C, *right_i32);
        else if (expr->token() == TOK_EQUALS)
          __ opcode(OP_EQ_C_PRI, *right_i32);
        return ValueDest::Pri;
      }

      uint64_t saved_pri = save(ValueDest::Pri);
      if (!emit_into(right, ValueDest::Alt))
        return ValueDest::Error;
      restore(saved_pri);

      if (expr->token() == TOK_PLUS)
        __ opcode(OP_ADD);
      else if (expr->token() == TOK_STAR)
        __ opcode(OP_SMUL);
      else if (expr->token() == TOK_EQUALS)
        __ opcode(OP_EQ);
      return ValueDest::Pri;
    }

    case TOK_SLASH:
    {
      // SDIV = pri / alt
      // SDIV_ALT = alt / pri
      //
      // Does it ever make sense to emit SDIV_ALT, if we have knowledge that
      // pri or alt might be spilled?

      if (!emit_into(left, ValueDest::Pri))
        return ValueDest::Error;

      uint64_t saved_pri = save(ValueDest::Pri);
      if (!emit_into(right, ValueDest::Alt))
        return ValueDest::Error;
      restore(saved_pri);

      __ opcode(OP_SDIV);
      return ValueDest::Pri;
    }

    case TOK_MINUS:
    case TOK_BITOR:
    case TOK_BITXOR:
    case TOK_BITAND:
    case TOK_SHL:
    case TOK_SHR:
    case TOK_USHR:
    case TOK_NOTEQUALS:
    case TOK_GT:
    case TOK_GE:
    case TOK_LT:
    case TOK_LE:
    {
      if (!emit_into(left, ValueDest::Pri))
        return ValueDest::Error;

      uint64_t saved_pri = save(ValueDest::Pri);
      if (!emit_into(right, ValueDest::Alt))
        return ValueDest::Error;
      restore(saved_pri);

      switch (expr->token()) {
        case TOK_MINUS:
          __ opcode(OP_SUB);
          break;
        case TOK_BITOR:
          __ opcode(OP_OR);
          break;
        case TOK_BITXOR:
          __ opcode(OP_XOR);
          break;
        case TOK_BITAND:
          __ opcode(OP_AND);
          break;
        case TOK_SHL:
          __ opcode(OP_SHL);
          break;
        case TOK_SHR:
          __ opcode(OP_SSHR);
          break;
        case TOK_USHR:
          __ opcode(OP_SHR);
          break;
        case TOK_NOTEQUALS:
          __ opcode(OP_NEQ);
          break;
        case TOK_GT:
          __ opcode(OP_SGRTR);
          break;
        case TOK_GE:
          __ opcode(OP_SGEQ);
          break;
        case TOK_LT:
          __ opcode(OP_SLESS);
          break;
        case TOK_LE:
          __ opcode(OP_SLEQ);
          break;
        default:
          assert(false);
          break;
      }
      return ValueDest::Pri;
    }

    default:
      cc_.report(expr->src()->loc(), rmsg::unimpl_kind) <<
        "smx-binexpr-tok" << TokenNames[expr->token()];
      return ValueDest::Error;
  }
}

ValueDest
SmxCompiler::emitUnary(sema::UnaryExpr* expr, ValueDest dest)
{
  sema::Expr* inner = expr->expr();

  switch (expr->token()) {
    case TOK_NEGATE:
    case TOK_NOT:
    case TOK_TILDE:
      if (!emit_into(inner, ValueDest::Pri))
        return ValueDest::Error;

      switch (expr->token()) {
        case TOK_NEGATE:
          __ opcode(OP_NEG);
          break;
        case TOK_NOT:
          __ opcode(OP_NOT);
          break;
        case TOK_TILDE:
          __ opcode(OP_INVERT);
          break;
        default:
          assert(false);
      }
      return ValueDest::Pri;

    default:
      cc_.report(expr->src()->loc(), rmsg::unimpl_kind) <<
        "smx-unary-tok" << TokenNames[expr->token()];
      return ValueDest::Error;
  }
}

ValueDest
SmxCompiler::emitTrivialCast(sema::TrivialCastExpr* expr, ValueDest dest)
{
  // Pass-through - we don't generate code for trivial casts, since the
  // bytecode is not typed.
  return emit(expr->expr(), dest);
}

ValueDest
SmxCompiler::emitCall(sema::CallExpr* expr, ValueDest dest)
{
  // We only support named callees right now (that is, the function cannot be
  // stored in a variable or as the result of an expression).
  sema::NamedFunctionExpr* callee = expr->callee()->asNamedFunctionExpr();
  assert(callee);

  FunctionSymbol* fun = callee->sym();
  ast::FunctionSignature* sig = fun->impl()->signature();

  // We have to kill pri/alt before entering the argument push sequence, since
  // otherwise we may misalign the arguments.
  will_kill(ValueDest::Pri);
  will_kill(ValueDest::Alt);

  // SourcePawn evaluates arguments right-to-left, probably not for any
  // semantic reason, but because of how the original compiler worked.
  // The authors wanted arguments to be laid out on the stack such that
  // argument 0 would be at address +0, argument 1 at address +4, etc,
  // probably to make handling variadic arguments slightly easier. Instead
  // of generating a series of moves, it would instead put markers around
  // the instruction stream where each individual argument was generated.
  // Then, it would reorder everything in between these markers, so that
  // everything pushed to the stack in the right order.
  //
  // It's not clear why this was chosen over moves - possibly it made
  // the code generator simpler, or possibly the compiler was initially
  // one-pass (and since it never had an AST, it wouldn't have known the
  // argument count).

  // TODO make sure we verify that call labels are bound
  sema::ExprList* args = expr->args();
  for (size_t i = args->length() - 1; i < args->length(); i--) {
    sema::Expr* expr = args->at(i);

    size_t opstack_size = operand_stack_.length();

    emit_into(expr, ValueDest::Stack);

    // Make sure emit_into does not cause any spills (or, if it did, that the
    // spills were cleaned up internally). Otherwise the stack will be
    // misaligned.
    if (opstack_size != operand_stack_.length()) {
      cc_.report(SourceLocation(), rmsg::regalloc_error) <<
        "argument pushed too many values onto the stack";
    }
  }

  if (sig->native()) {
    // Mark the native as used.
    if (!fun->impl()->address()->used())
      natives_.append(FunctionEntry(fun->name(), fun->impl()));

    __ sysreq_n(fun->impl()->address(), (uint32_t)args->length());
    assert(fun->impl()->address()->used());
  } else {
    __ opcode(OP_CALL, fun->impl()->address());
  }

  return ValueDest::Pri;
}

void
SmxCompiler::generateData(ast::VarDecl* decl)
{
  VariableSymbol* sym = decl->sym();
  assert(HasSimpleCellStorage(sym->type()));

  int32_t address = int32_t(data_.pos());
  sym->allocate(StorageClass::Global, address);

  data_.write<cell_t>(0);

  sema::Expr* init = decl->sema_init();
  if (!init)
    return;

  uint8_t* bytes = data_.bytes() + sym->address();
  switch (init->kind()) {
    case sema::ExprKind::ConstValue:
    {
      sema::ConstValueExpr* expr = init->toConstValueExpr();
      const BoxedValue& value = expr->value();
      if (value.isInteger()) {
        *reinterpret_cast<int32_t*>(bytes) = (int32_t)value.toInteger().asSigned();
      } else {
        cc_.report(decl->loc(), rmsg::unimpl_kind) <<
          "smx-gen-data" << "value type";
      }
      break;
    }
  }
}

void
SmxCompiler::will_kill(ValueDest dest)
{
  if (dest == ValueDest::Stack)
    return;

  assert(dest == ValueDest::Pri || dest == ValueDest::Alt);

  uint64_t* slot = nullptr;
  OPCODE op = OP_NOP;
  if (dest == ValueDest::Pri) {
    slot = &pri_value_;
    op = OP_PUSH_PRI;
  } else {
    slot = &alt_value_;
    op = OP_PUSH_ALT;
  }

  // We don't bother asserting that the slot is a particular value. We just
  // push it. If stuff is unbalanced, it will be caught in emitStatement or in
  // restore().
  if (*slot)
    __ opcode(op);

  *slot = 0;
}

uint64_t
SmxCompiler::save(ValueDest dest)
{
  assert(dest == ValueDest::Pri || dest == ValueDest::Alt);

  SValue value(dest);
  operand_stack_.append(value);

  uint64_t* slot = (dest == ValueDest::Pri)
                   ? &pri_value_
                   : &alt_value_;
  if (*slot) {
    cc_.report(SourceLocation(), rmsg::regalloc_error) <<
      "saving register without a clobber";
  }

  *slot = value.id();
  assert(pri_value_ != alt_value_);

  return value.id();
}

// Restore a register that was previously saved.
void
SmxCompiler::restore(uint64_t id)
{
  if (operand_stack_.empty() || operand_stack_.back().id() != id) {
    cc_.report(SourceLocation(), rmsg::regalloc_error) <<
      "restored register is not top of operand stack";
    return;
  }

  SValue value = operand_stack_.popCopy();
  assert(value.where() == ValueDest::Pri || value.where() == ValueDest::Alt);

  uint64_t* slot = nullptr;
  OPCODE op = OP_NOP;
  if (value.where() == ValueDest::Pri) {
    slot = &pri_value_;
    op = OP_POP_PRI;
  } else {
    slot = &alt_value_;
    op = OP_POP_ALT;
  }

  if (*slot == value.id()) {
    // The value hasn't been changed or killed, so we can just clear it.
    *slot = 0;
    return;
  }

  // If another value is occupying this register, it means we forgot to kill
  // it somewhere. Or we have an antipattern like:
  //    save pri -> A
  //    kill pri
  //    save pri -> B
  //    restore A
  //
  // But this should have been caught above via the operand stack.
  if (*slot != 0) {
    cc_.report(SourceLocation(), rmsg::regalloc_error) <<
      "restoring saved register would overwrite another value";
    return;
  }

  __ opcode(op);
  *slot = 0;
}

static bool
HasSimpleCellStorage(Type* type)
{
  switch (type->canonicalKind()) {
    case Type::Kind::Primitive:
    case Type::Kind::Enum:
    case Type::Kind::Unchecked:
    case Type::Kind::Function:
    case Type::Kind::MetaFunction:
      return true;
    default:
      return false;
  }
}

void
SmxCompiler::store_into(VariableSymbol* sym, sema::Expr* init)
{
  Type* type = sym->type();
  assert(HasSimpleCellStorage(type));

  switch (sym->scope()->kind()) {
    case Scope::Block:
      emit_into(init, ValueDest::Pri);
      __ opcode(OP_STOR_S_PRI, sym->address());
      break;

    default:
      cc_.report(SourceLocation(), rmsg::unimpl_kind) <<
        "store-int-scope-kind" << int32_t(sym->scope()->kind());
  }
}

int32_t
SmxCompiler::compute_storage_size(Type* type)
{
  if (HasSimpleCellStorage(type))
    return sizeof(cell_t);

  cc_.report(SourceLocation(), rmsg::unimpl_kind) <<
    "smx-storage-size" << int32_t(type->canonicalKind());
  return 0;
}

int
SmxCompiler::sort_functions(const void *a1, const void *a2)
{
  FunctionEntry &f1 = *(FunctionEntry *)a1;
  FunctionEntry &f2 = *(FunctionEntry *)a2;
  return strcmp(f1.name->chars(), f2.name->chars());
}

} // namespace sp
