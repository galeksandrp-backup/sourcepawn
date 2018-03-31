// vim: set ts=2 sw=2 tw=99 et:
// 
// Copyright (C) 2012-2014 AlliedModders LLC and David Anderson
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
#include "semantic-analysis.h"
#include "scopes.h"
#include "symbols.h"

namespace sp {

using namespace ke;
using namespace ast;

// :TODO: constant folding

SemanticAnalysis::SemanticAnalysis(CompileContext &cc, TranslationUnit *tu)
 : cc_(cc),
   pool_(cc.pool()),
   types_(cc.types()),
   tu_(tu),
   fs_(nullptr)
{
}

sema::Program*
SemanticAnalysis::analyze()
{
  if (!walkAST())
    return nullptr;

  sema::Program* program = new (pool_) sema::Program;
  program->functions = ke::Move(global_functions_);
  program->natives = ke::Move(global_natives_);
  return program;
}

bool
SemanticAnalysis::walkAST()
{
  ParseTree *tree = tu_->tree();
  StatementList *statements = tree->statements();
  for (size_t i = 0; i < statements->length(); i++) {
    Statement *stmt = statements->at(i);
    switch (stmt->kind()) {
      case AstKind::kFunctionStatement:
      {
        FunctionStatement* fun = stmt->toFunctionStatement();
        visitFunctionStatement(fun);
        break;
      }
      default:
        cc_.report(stmt->loc(), rmsg::unimpl_kind) <<
          "sema-ast-walk" << stmt->kindName();
        break;
    }
    if (!cc_.canContinueProcessing())
      return false;
  }
  return cc_.phasePassed();
}

void
SemanticAnalysis::visitFunctionStatement(FunctionStatement *node)
{
  FunctionSymbol *sym = node->sym();

  assert(!fs_);

  if (!fs_ && sym->shadows()) {
    // We are the root in a series of shadowed functions.
    analyzeShadowedFunctions(sym);
  }

  if (!node->body()) {
    if (node->signature()->native())
      global_natives_.append(node);
    return;
  }

  FuncState state(&fs_, node);
  visitBlockStatement(node->body());

  if (fs_->return_status == ReturnStatus::All)
    node->set_guaranteed_return();

  assert(fs_->return_status != ReturnStatus::Mixed);
  global_functions_.append(node);
}

// :TODO: write tests for this.
void
SemanticAnalysis::analyzeShadowedFunctions(FunctionSymbol *sym)
{
  // We do not yet support overloading, so two functions with the same name
  // and a body are illegal. We consider natives to be implemented.
  FunctionStatement *impl = nullptr;

  // We support non-native implementations of a forwarded function.
  FunctionStatement *forward = nullptr;

  for (size_t i = 0; i < sym->shadows()->length(); i++) {
    FunctionStatement *stmt = sym->shadows()->at(i);
    switch (stmt->token()) {
      case TOK_FORWARD:
        if (forward) {
          cc_.report(stmt->loc(), rmsg::function_redeclared)
            << stmt->name()
            << (cc_.note(forward->loc(), rmsg::previous_location));
          continue;
        }
        forward = stmt;
        break;
      case TOK_NATIVE:
      case TOK_FUNCTION:
        if (impl) {
          cc_.report(stmt->loc(), rmsg::function_redeclared)
            << stmt->name()
            << (cc_.note(impl->loc(), rmsg::previous_location));
          continue;
        }
        impl = stmt;
        break;
      default:
        assert(false);
        break;
    }
  }

  // If we have both an impl and a forward, make sure they match.
  if (impl && forward)
    checkForwardedFunction(forward, impl);
}

void
SemanticAnalysis::checkForwardedFunction(FunctionStatement *forward, FunctionStatement *impl)
{
  // SP1 didn't check these. We tighten up the semantics a bit for SP2.
  if (impl->token() == TOK_NATIVE) {
    cc_.report(impl->loc(), rmsg::illegal_forward_native)
      << impl->name()
      << cc_.note(forward->loc(), rmsg::previous_location);
    return;
  }
   
  if (!(impl->attrs() & DeclAttrs::Public)) {
    cc_.report(impl->loc(), rmsg::illegal_forward_func)
      << impl->name()
      << cc_.note(forward->loc(), rmsg::previous_location);
    return;
  }

  FunctionSignature *fwdSig = forward->signature();
  FunctionSignature *implSig = impl->signature();

  if (!matchForwardSignatures(fwdSig, implSig)) {
    cc_.report(impl->loc(), rmsg::forward_signature_mismatch)
      << impl->name()
      << cc_.note(forward->loc(), rmsg::previous_location);
    return;
  }
}

bool
SemanticAnalysis::matchForwardSignatures(FunctionSignature *fwdSig, FunctionSignature *implSig)
{
  // Due to SourceMod oddness, and the implementation detail that arguments are
  // pushed in reverse order, the impl function is allowed to leave off any
  // number of arguments. But, it cannot have more arguments.
  if (fwdSig->parameters()->length() < implSig->parameters()->length())
    return false;

  // We allow return types to differ iff the forward's type is void and the
  // impl function is implicit-int.
  Type *fwdRetType = fwdSig->returnType().resolved();
  Type *implRetType = implSig->returnType().resolved();
  if (!matchForwardReturnTypes(fwdRetType, implRetType))
    return false;

  return true;
}

bool
SemanticAnalysis::matchForwardReturnTypes(Type *fwdRetType, Type *implRetType)
{
  if (AreTypesEquivalent(fwdRetType, implRetType, Qualifiers::None))
    return true;
  if ((fwdRetType->isVoid() || fwdRetType->isImplicitInt()) && implRetType->isImplicitVoid())
    return true;
  return false;
}

void
SemanticAnalysis::visitBlockStatement(BlockStatement* node)
{
  for (size_t i = 0; i < node->statements()->length(); i++) {
    Statement* ast_stmt = node->statements()->at(i);
    visitStatement(ast_stmt);
  }
}

void
SemanticAnalysis::visitStatement(Statement* node)
{
  switch (node->kind()) {
    case AstKind::kReturnStatement:
      visitReturnStatement(node->toReturnStatement());
      break;
    case AstKind::kExpressionStatement:
      visitExpressionStatement(node->toExpressionStatement());
      break;
    case AstKind::kVarDecl:
      visitVarDecl(node->toVarDecl());
      break;
    default:
      cc_.report(node->loc(), rmsg::unimpl_kind) <<
        "sema-visit-stmt" << node->kindName();
      break;
  }
}

sema::Expr*
SemanticAnalysis::visitExpression(Expression* node)
{
  switch (node->kind()) {
    case AstKind::kIntegerLiteral:
      return visitIntegerLiteral(node->toIntegerLiteral());
    case AstKind::kBinaryExpression:
      return visitBinaryExpression(node->toBinaryExpression());
    case AstKind::kCallExpression:
      return visitCallExpression(node->toCallExpression());
    case AstKind::kNameProxy:
      return visitNameProxy(node->toNameProxy());
    case AstKind::kUnaryExpression:
      return visitUnaryExpression(node->toUnaryExpression());
    default:
      assert(false);
  }
  return nullptr;
}

void
SemanticAnalysis::visitVarDecl(VarDecl* node)
{
  VariableSymbol* sym = node->sym();

  // :TODO: unused var analysis

  sema::Expr* init = nullptr;
  if (node->initialization()) {
    if ((init = initializer(node->initialization(), sym->type())) == nullptr)
      return;
    node->set_sema_init(init);
  }
}

void
SemanticAnalysis::visitReturnStatement(ReturnStatement* node)
{
  FunctionSignature* sig = fs_->sig;
  Type* returnType = sig->returnType().resolved();

  fs_->return_status = ReturnStatus::All;

  if (returnType->isVoid()) {
    if (node->expr())
      cc_.report(node->loc(), rmsg::returned_in_void_function);
    return;
  }

  if (!node->expr())
    cc_.report(node->loc(), rmsg::need_return_value);

  sema::Expr* expr = visitExpression(node->expr());

  if (!(expr = coerce(expr, returnType, Coercion::Return)))
    return;

  node->set_sema_expr(expr);
}

void
SemanticAnalysis::visitExpressionStatement(ExpressionStatement* node)
{
  sema::Expr* expr = visitExpression(node->expr());
  if (!expr)
    return;
  node->set_sema_expr(expr);
}

sema::CallExpr*
SemanticAnalysis::visitCallExpression(CallExpression* node)
{
  // Call expressions are complicated because we only support very specific
  // patterns. We sniff them out here.
  sema::Expr* callee = nullptr;
  if (NameProxy* proxy = node->callee()->asNameProxy()) {
    if (FunctionSymbol* sym = proxy->sym()->asFunction()) {
      assert(sym->scope()->kind() == Scope::Global);
      callee = new (pool_) sema::NamedFunctionExpr(proxy, sym->impl()->signature_type(), sym);
    }
  }

  if (!callee || !callee->type()->isFunction()) {
    cc_.report(node->loc(), rmsg::callee_is_not_function);
    return nullptr;
  }

  FunctionType* fun_type = callee->type()->asFunction();
  ast::FunctionSignature* sig = fun_type->signature();
  ast::ParameterList* params = sig->parameters();

  ast::ExpressionList* ast_args = node->arguments();

  if (params->length() != ast_args->length()) {
    cc_.report(node->loc(), rmsg::argcount_not_supported);
    return nullptr;
  }

  sema::ExprList* args = new (pool_) sema::ExprList();
  for (size_t i = 0; i < ast_args->length(); i++) {
    ast::Expression* ast_arg = ast_args->at(i);
    sema::Expr* arg = visitExpression(ast_arg);
    if (!arg)
      continue;
    if (!(arg = coerce(arg, params->at(i)->type(), Coercion::Arg)))
      continue;
    args->append(arg);
  }

  return new (pool_) sema::CallExpr(node, fun_type->returnType(), callee, args);
}

sema::ConstValueExpr*
SemanticAnalysis::visitIntegerLiteral(IntegerLiteral* node)
{
  // :TODO: test overflow
  int32_t value;
  if (!IntValue::SafeCast(node->value(), &value)) {
    cc_.report(node->loc(), rmsg::int_literal_out_of_range);
    return nullptr;
  }

  BoxedValue b(IntValue::FromValue(value));

  Type* i32type = types_->getPrimitive(PrimitiveType::Int32);
  return new (pool_) sema::ConstValueExpr(node, i32type, b);
}

sema::Expr*
SemanticAnalysis::visitNameProxy(ast::NameProxy* node)
{
  Symbol* base_sym = node->sym();
  VariableSymbol* sym = base_sym->asVariable();
  if (!sym) {
    cc_.report(node->loc(), rmsg::unimpl_kind) <<
      "name-proxy-symbol" << node->kindName();
    return nullptr;
  }

  return new (pool_) sema::VarExpr(node, sym->type(), sym);
}

sema::BinaryExpr*
SemanticAnalysis::visitBinaryExpression(BinaryExpression* node)
{
  sema::Expr* left = visitExpression(node->left());
  if (!left)
    return nullptr;

  sema::Expr* right = visitExpression(node->right());
  if (!right)
    return nullptr;

  assert(left->type() == right->type());

  Type* type = nullptr;
  switch (node->token()) {
    case TOK_PLUS:
    case TOK_MINUS:
    case TOK_STAR:
    case TOK_SLASH:
    case TOK_PERCENT:
    case TOK_AMPERSAND:
    case TOK_BITOR:
    case TOK_BITXOR:
    case TOK_SHR:
    case TOK_USHR:
    case TOK_SHL:
      type = left->type();
      break;
    case TOK_EQUALS:
    case TOK_NOTEQUALS:
    case TOK_GT:
    case TOK_GE:
    case TOK_LT:
    case TOK_LE:
      type = types_->getPrimitive(PrimitiveType::Bool);
      break;
    default:
      cc_.report(node->loc(), rmsg::unimpl_kind) <<
        "sema-bin-token" << TokenNames[node->token()];
      return nullptr;
  }

  return new (pool_) sema::BinaryExpr(node, type, node->token(), left, right);
}

sema::Expr*
SemanticAnalysis::visitUnaryExpression(ast::UnaryExpression* node)
{
  sema::Expr* expr = visitExpression(node->expression());
  if (!expr)
    return nullptr;

  Type* type = expr->type();
  assert(type->primitive() == PrimitiveType::Int32);

  return new (pool_) sema::UnaryExpr(node, type, node->token(), expr);
}

sema::Expr*
SemanticAnalysis::initializer(ast::Expression* node, Type* type)
{
  sema::Expr* expr = visitExpression(node);
  if (!expr)
    return nullptr;

  return coerce(expr, type, Coercion::Assignment);
}

sema::Expr*
SemanticAnalysis::coerce(sema::Expr* expr, Type* to, Coercion context)
{
  Type* from = expr->type();

  if (from == to)
    return expr;

  sema::Expr* result = coerce_inner(expr, from, to, context);
  if (!result) {
    cc_.report(expr->src()->loc(), rmsg::cannot_coerce) << from << to;
    return nullptr;

  }
  return result;
}

sema::Expr*
SemanticAnalysis::coerce_inner(sema::Expr* expr,
                               Type* from,
                               Type* to,
                               Coercion context)
{
  if (to->isPrimitive()) {
    if (!from->isPrimitive())
      return nullptr;
    if (from->primitive() == to->primitive())
      return expr;
    if (from->primitive() == PrimitiveType::Bool ||
        from->primitive() == PrimitiveType::Char)
    {
      return new (pool_) sema::TrivialCastExpr(expr->src(), to, expr);
    }
    return nullptr;
  }

  return nullptr;
}

#if 0
void
SemanticAnalysis::visitExpressionStatement(ExpressionStatement *node)
{
  Expression *expr = node->expr();

  expr->accept(this);

  // if (!expr->hasSideEffects())
  //   cc_.report(node->loc(), rmsg::expr_has_no_side_effects);
}
#endif

#if 0
void
SemanticAnalysis::visitCallExpr(CallExpr *node)
{
  // :TODO: we must verify that the callee is an implemented scripted func.
  Expression *callee = visitForRValue(node->callee());
  if (!callee)
    return;
  if (!callee->type()->isFunction()) {
    cc_.report(node->loc(), rmsg::callee_is_not_a_function)
      << callee->type();
    return;
  }
  node->setCallee(callee);

  FunctionSignature *sig = callee->type()->toFunction()->signature();
  checkCall(sig, node->arguments());

  Type *returnType = sig->returnType().resolved();
  node->setOutput(returnType, VK::rvalue);

  // We mark calls as always having side effects.
  node->setHasSideEffects();
}
#endif

void
SemanticAnalysis::checkCall(FunctionSignature *sig, ExpressionList *args)
{
  VarDecl *vararg = nullptr;
  for (size_t i = 0; i < args->length(); i++) {
    Expression *expr = args->at(i);

    VarDecl *arg = nullptr;
    if (i >= sig->parameters()->length()) {
      if (!vararg) {
        cc_.report(expr->loc(), rmsg::wrong_argcount)
          << args->length(), sig->parameters()->length();
        return;
      }
      arg = vararg;
    } else {
      arg = sig->parameters()->at(i);
    }
    (void)arg;

#if 0
    visitForValue(expr);

    Coercion cr(cc_,
                Coercion::Reason::arg,
                expr,
                arg->te().resolved());
    if (cr.coerce() != Coercion::Result::ok) {
      auto builder = cc_.report(expr->loc(), rmsg::cannot_coerce_for_arg)
        << expr->type()
        << arg->te().resolved();

      if (i < args->length() && arg->name())
        builder << arg->name();
      else
        builder << i;

      builder << cr.diag(expr->loc());
      break;
    }

    // Rewrite the tree for the coerced result.
    args->at(i) = cr.output();
#endif
  }
}

#if 0
void
SemanticAnalysis::visitNameProxy(NameProxy *proxy)
{
  Symbol *binding = proxy->sym();
  switch (binding->kind()) {
    case Symbol::kType:
      cc_.report(proxy->loc(), rmsg::cannot_use_type_as_value)
        << binding->asType()->type();
      break;

    case Symbol::kConstant:
    {
      //ConstantSymbol *sym = binding->toConstant();
      //proxy->setOutput(sym->type(), VK::rvalue);
      break;
    }

    case Symbol::kFunction:
    {
      FunctionSymbol *sym = binding->toFunction();
      FunctionStatement *decl = sym->impl();
      if (!decl) {
        cc_.report(proxy->loc(), rmsg::function_has_no_impl)
          << sym->name();
        break;
      }

      if (!decl->type())
        decl->setType(FunctionType::New(decl->signature()));

      // Function symbols are clvalues, since they are named.
      // :TODO:
      proxy->setOutput(decl->type(), VK::lvalue);
      break;
    }

    default:
      assert(false);
  }
}
#endif

#if 0
void
SemanticAnalysis::visitStringLiteral(StringLiteral *node)
{
  // Build a constant array for the character string.
  Type *charType = types_->getPrimitive(PrimitiveType::Char);
  ArrayType *arrayType = types_->newArray(charType, node->arrayLength());
  Type *litType = types_->newQualified(arrayType, Qualifiers::Const);

  // Returned value is always an rvalue.
  node->setOutput(litType, VK::rvalue);
}
#endif

} // namespace sp
