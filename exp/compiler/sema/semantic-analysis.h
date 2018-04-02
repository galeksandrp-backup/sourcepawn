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
#ifndef _include_semantic_analysis_h_
#define _include_semantic_analysis_h_

#include "parser/ast.h"
#include "sema/expressions.h"
#include "sema/program.h"

namespace sp {

class CompileContext;
class PoolAllocator;
class TranslationUnit;
class TypeManager;

using namespace ast;

class SemanticAnalysis
{
 public:
  SemanticAnalysis(CompileContext &cc, TranslationUnit *unit);

  sema::Program* analyze();

 private:
  bool walkAST();

  void visitFunctionStatement(FunctionStatement* node);
  void visitBlockStatement(BlockStatement* node);
  void visitStatement(Statement* node);
  void visitReturnStatement(ReturnStatement* node);
  void visitExpressionStatement(ExpressionStatement* node);
  void visitVarDecl(VarDecl* node);
  void visitWhileStatement(WhileStatement* node);
  void visitIfStatement(IfStatement* node);
  void visitBreakStatement(BreakStatement* node);

  sema::Expr* visitExpression(Expression* node);
  sema::ConstValueExpr* visitIntegerLiteral(IntegerLiteral* node);
  sema::BinaryExpr* visitBinaryExpression(BinaryExpression* node);
  sema::CallExpr* visitCallExpression(ast::CallExpression* node);
  sema::Expr* visitNameProxy(ast::NameProxy* node);
  sema::Expr* visitUnaryExpression(ast::UnaryExpression* node);
  sema::Expr* visitStringLiteral(ast::StringLiteral* node);

 private:
  void analyzeShadowedFunctions(FunctionSymbol *sym);
  void checkForwardedFunction(FunctionStatement *forward, FunctionStatement *impl); 
  bool matchForwardSignatures(FunctionSignature *fwdSig, FunctionSignature *implSig);
  bool matchForwardReturnTypes(Type *fwdRetType, Type *implRetType);

  sema::Expr* check_arg(sema::Expr* arg, VarDecl* param);
  sema::Expr* check_array_arg(sema::Expr* arg, VarDecl* param);

  enum class Coercion {
    Arg,
    Assignment,
    Return,
    Test,
    Expr
  };
  sema::Expr* coerce(sema::Expr* from, Type* to, Coercion context);
  sema::Expr* coerce_inner(sema::Expr* from_expr,
                           Type* from,
                           Type* to,
                           Coercion context);
  sema::Expr* initializer(ast::Expression* expr, Type* type);

  // No-op function to breakpoint on type errors.
  sema::Expr* no_conversion(sema::Expr* expr, Type* from, Type* to);

 private:
  enum class ReturnStatus {
    None,   // No return statements.
    Mixed,  // Some returns.
    All     // All paths return.
  };

  struct FuncState : StackLinked<FuncState>
  {
    FuncState(FuncState **prev, FunctionNode *node)
     : StackLinked<FuncState>(prev),
       fun(node),
       sig(node->signature()),
       return_status(ReturnStatus::None)
    {}

    FunctionNode *fun;
    FunctionSignature *sig;

    // This tracks how the current control-flow path returns.
    ReturnStatus return_status;
  };

 private:
  CompileContext &cc_;
  PoolAllocator &pool_;
  TypeManager *types_;
  TranslationUnit *tu_;

  FuncState *fs_;

  ke::Vector<ast::FunctionStatement*> global_functions_;
  ke::Vector<ast::VarDecl*> global_vars_;

  size_t loop_depth_;
};

} // namespace sp

#endif // _include_semantic_analysis_h_
