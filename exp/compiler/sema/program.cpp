// vim: set sts=2 ts=8 sw=2 tw=99 et:
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
#include "program.h"
#include "expressions.h"
#include "parser/ast.h"

namespace sp {

class SemaPrinter : public ast::StrictAstVisitor
{
 public:
  explicit SemaPrinter(FILE* fp)
   : fp_(fp),
     level_(0)
  {}

  void print(sema::Program* program) {
    for (ast::FunctionStatement* stmt : program->functions)
      printFunction(stmt);
  }

 private:
  void printFunction(ast::FunctionStatement* node) {
    prefix();
    fprintf(fp_, "- FunctionStatement (%s)\n", node->name()->chars());
    indent();
    {
      prefix();
      dump(node->signature());
      if (node->body())
        visitBlockStatement(node->body());
    }
    unindent();
  }

  void visitBlockStatement(ast::BlockStatement* body) override {
    prefix();
    fprintf(fp_, "- BlockStatement\n");
    indent();
    {
      ast::StatementList* statements = body->statements();
      for (size_t i = 0; i < statements->length(); i++) {
        ast::Statement* stmt = statements->at(i);
        stmt->accept(this);
      }
    }
    unindent();
  }

  void visitVarDecl(ast::VarDecl* stmt) override {
     prefix();
     fprintf(fp_, "- VarDecl: %s\n", BuildTypeName(stmt->sym()->type(), stmt->sym()->name()).chars());
     indent();
     {
       prefix();
       fprintf(fp_, "=\n");
       if (sema::Expr* expr = stmt->sema_init()) {
         prefix();
         printExpr(expr);
       }
     }
     unindent();
  }

  void visitReturnStatement(ast::ReturnStatement* stmt) override {
    prefix();
    fprintf(fp_, "- ReturnStatement\n");
    indent();
    {
      sema::Expr* expr = stmt->sema_expr();
      if (!expr)
        fprintf(fp_, "(void)\n");
      else
        printExpr(expr);
    }
    unindent();
  }

  void visitWhileStatement(ast::WhileStatement* stmt) override {
    prefix();
    fprintf(fp_, "- WhileStatement\n");
    indent();
    {
      prefix();
      fprintf(fp_, "%s\n", TokenNames[stmt->token()]);
      printExpr(stmt->sema_cond());
      stmt->body()->accept(this);
    }
    unindent();
  }

  void visitExpressionStatement(ast::ExpressionStatement* stmt) override {
    prefix();
    fprintf(fp_, "- ExpressionStatement\n");
    indent();
    {
      printExpr(stmt->sema_expr());
    }
    unindent();
  }

  void printExpr(sema::Expr* expr) {
    switch (expr->kind()) {
      case sema::ExprKind::ConstValue:
        printConstValue(expr->toConstValueExpr());
        break;
      case sema::ExprKind::Binary:
        printBinary(expr->toBinaryExpr());
        break;
      case sema::ExprKind::Unary:
        printUnary(expr->toUnaryExpr());
        break;
      case sema::ExprKind::Call:
        printCall(expr->toCallExpr());
        break;
      case sema::ExprKind::NamedFunction:
        printNamedFunction(expr->toNamedFunctionExpr());
        break;
      case sema::ExprKind::Var:
        printVar(expr->toVarExpr());
        break;
      case sema::ExprKind::TrivialCast:
        printTrivialCast(expr->toTrivialCastExpr());
        break;
      case sema::ExprKind::String:
        printString(expr->toStringExpr());
        break;
      default:
        assert(false);
    }
  }

  void printConstValue(sema::ConstValueExpr* expr) {
    enter(expr, expr->type());
    indent();
    {
      const BoxedValue& value = expr->value();
      prefix();
      dump(value);
      fprintf(fp_, "\n");
    }
    unindent();
  }

  void printCall(sema::CallExpr* expr) {
    enter(expr, expr->type());
    indent();
    {
      printExpr(expr->callee());
      for (size_t i = 0; i < expr->args()->length(); i++)
        printExpr(expr->args()->at(i));
    }
    unindent();
  }

  void printNamedFunction(sema::NamedFunctionExpr* expr) {
    enter(expr, expr->type());
    indent();
    {
      prefix();
      fprintf(fp_, "%s\n", expr->sym()->name()->chars());
    }
    unindent();
  }

  void printBinary(sema::BinaryExpr* expr) {
    enter(expr, expr->type());
    indent();
    {
      prefix();
      fprintf(fp_, "\"%s\"\n", TokenNames[expr->token()]);
      printExpr(expr->left());
      printExpr(expr->right());
    }
    unindent();
  }

  void printUnary(sema::UnaryExpr* expr) {
    enter(expr, expr->type());
    indent();
    {
      prefix();
      fprintf(fp_, "\"%s\"\n", TokenNames[expr->token()]);
      printExpr(expr->expr());
    }
    unindent();
  }

  void printTrivialCast(sema::TrivialCastExpr* expr) {
    enter(expr, expr->type());
    indent();
    {
      printExpr(expr->expr());
    }
    unindent();
  }

  void printString(sema::StringExpr* expr) {
    enter(expr, expr->type());
    indent();
    {
      // Note: this is gross because we don't print \n or \t.
      prefix();
      fprintf(fp_, "\"");
      const char* ptr = expr->literal()->chars();
      while (*ptr) {
        if (*ptr == '\n') {
          fprintf(fp_, "\\n");
        } else if (*ptr == '\t') {
          fprintf(fp_, "\\t");
        } else {
          fprintf(fp_, "%c", *ptr);
        }
        ptr++;
      }
      fprintf(fp_, "\"\n");
    }
    unindent();
  }

  void printVar(sema::VarExpr* expr) {
    prefix();
    AString str = BuildTypeName(expr->type(), nullptr);
    fprintf(fp_, "- %s %s (%s)\n",
      expr->prettyName(),
      expr->sym()->name()->chars(),
      str.chars());
  }

  void dump(const BoxedValue& value) {
    switch (value.kind()) {
      case BoxedValue::Kind::Bool:
        fprintf(fp_, "%s", value.toBool() ? "true" : "false");
        break;
      case BoxedValue::Kind::Integer:
      {
        const IntValue& iv = value.toInteger();
        if (iv.isSigned())
          fprintf(fp_, "%" KE_FMT_I64, iv.asSigned());
        else
          fprintf(fp_, "%" KE_FMT_U64, iv.asUnsigned());
        break;
      }
      default:
        assert(false);
    }
  }

  void enter(sema::Expr* expr, Type* type) {
    prefix();
    AString str = BuildTypeName(type, nullptr);
    fprintf(fp_, "- %s (%s)\n", expr->prettyName(), str.chars());
  }

  void dump(const ast::TypeExpr& te, Atom *name) {
    AString str = BuildTypeName(te.resolved(), name);
    fprintf(fp_, "%s", str.chars());
  }

  void dump(ast::FunctionSignature *sig) {
    dump(sig->returnType(), nullptr);
    if (!sig->parameters()->length()) {
      fprintf(fp_, " ()\n");
      return;
    }
    fprintf(fp_, " (\n");
    indent();
    for (size_t i = 0; i < sig->parameters()->length(); i++) {
      prefix();
      ast::VarDecl *param = sig->parameters()->at(i);
      dump(param->te(), param->name());
      fprintf(fp_, "\n");
    }
    unindent();
    prefix();
    fprintf(fp_, ")");
  }

 private:
  void prefix() {
    for (size_t i = 0; i < level_; i++)
      fprintf(fp_, "  ");
  }
  void indent() {
    level_++;
  }
  void unindent() {
    level_--;
  }

 private:
  FILE* fp_;
  size_t level_;
}; 

void
sema::Program::dump(FILE* fp)
{
  SemaPrinter printer(fp);
  printer.print(this);
}

} // namespace sp
