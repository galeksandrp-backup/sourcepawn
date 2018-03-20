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
#include "smx-compiler.h"
#include <smx/smx-v1.h>
#include <sp_vm_types.h>

#define __ masm_.

namespace sp {

typedef SmxListSection<sp_file_natives_t> SmxNativeSection;
typedef SmxListSection<sp_file_publics_t> SmxPublicSection;
typedef SmxListSection<sp_file_pubvars_t> SmxPubvarSection;
typedef SmxBlobSection<sp_file_data_t> SmxDataSection;
typedef SmxBlobSection<sp_file_code_t> SmxCodeSection;

SmxCompiler::SmxCompiler(CompileContext& cc, sema::Program* program)
 : cc_(cc),
   program_(program)
{
  names_ = new SmxNameTable(".names");
  builder_.add(names_);
}

bool
SmxCompiler::compile()
{
  // This is always the first opcode, so instruction 0 is invalid.
  __ opcode(OP_HALT);

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

  assert(masm_.buffer_length() % sizeof(cell_t) == 0);
  assert(data_.size() % sizeof(cell_t) == 0);

  RefPtr<SmxCodeSection> code = new SmxCodeSection(".code");
  code->header().codesize = masm_.buffer_length();
  code->header().cellsize = sizeof(cell_t);
  code->header().codeversion = SmxConsts::CODE_VERSION_JIT_1_1;
  code->header().flags = CODEFLAG_DEBUG;
  code->header().main = 0;
  code->header().code = sizeof(sp_file_code_t);
  code->setBlob(masm_.buffer(), masm_.buffer_length());
  builder_.add(code);

  // Ensure the data section has at least one value.
  // :TODO: clean up data handling
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
  __ bind(fun->address());
  __ opcode(OP_PROC);

  generateBlock(fun->body());

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
  switch (stmt->kind()) {
    case ast::AstKind::kReturnStatement:
      generateReturn(stmt->toReturnStatement());
      break;
    default:
      assert(false);
  }
}

void
SmxCompiler::generateBlock(ast::BlockStatement* block)
{
  ast::StatementList* statements = block->statements();
  for (size_t i = 0; i < statements->length(); i++) {
    ast::Statement* stmt = statements->at(i);
    generateStatement(stmt);
  }
}

void
SmxCompiler::generateReturn(ast::ReturnStatement* stmt)
{
  // :TODO: verify stack depth
  emit_into(stmt->sema_expr(), ValueDest::Pri);
  __ opcode(OP_RETN);
}

bool
SmxCompiler::emit_into(sema::Expr* expr, ValueDest dest)
{
  ValueDest actual = emit(expr, dest);
  if (actual == ValueDest::Error)
    return false;

  assert(actual == dest);
  return true;
}

auto
SmxCompiler::emit(sema::Expr* expr, ValueDest dest) -> ValueDest
{
  switch (expr->kind()) {
  case sema::ExprKind::ConstValue:
    return emitConstValue(expr->toConstValueExpr(), dest);
  default:
    assert(false);
    return ValueDest::Error;
  }
}

auto
SmxCompiler::emitConstValue(sema::ConstValueExpr* expr, ValueDest dest) -> ValueDest
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

  switch (dest) {
  case ValueDest::Pri:
    __ opcode(OP_CONST_PRI, value);
    return dest;
  case ValueDest::Alt:
    __ opcode(OP_CONST_ALT, value);
    return dest;
  case ValueDest::Stack:
    __ opcode(OP_PUSH_C, value);
    return dest;
  default:
    assert(false);
  }
}

int
SmxCompiler::sort_functions(const void *a1, const void *a2)
{
  FunctionEntry &f1 = *(FunctionEntry *)a1;
  FunctionEntry &f2 = *(FunctionEntry *)a2;
  return strcmp(f1.name->chars(), f2.name->chars());
}

} // namespace sp
