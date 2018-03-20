// vim: set sts=2 ts=8 sw=2 tw=99 et:
// 
// Copyright (C) 2012 David Anderson
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

#ifndef _include_sourcepawn_emit_emitter_h_
#define _include_sourcepawn_emit_emitter_h_

#include "sema/expressions.h"
#include "sema/program.h"
#include "smx-assembly-buffer.h"
#include "smx-builder.h"

namespace sp {

class CompileContext;

class SmxCompiler
{
public:
  SmxCompiler(CompileContext& cc, sema::Program* program);

  bool compile();
  bool emit(ISmxBuffer* buffer);

private:
  void generate(ast::FunctionStatement* fun);

  void generateStatement(ast::Statement* stmt);
  void generateBlock(ast::BlockStatement* block);
  void generateReturn(ast::ReturnStatement* stmt);

  enum class ValueDest {
    Pri,
    Alt,
    Stack,
    Error
  };
  bool emit_into(sema::Expr* expr, ValueDest dest);

  ValueDest emit(sema::Expr* expr, ValueDest dest);
  ValueDest emitConstValue(sema::ConstValueExpr* expr, ValueDest dest);

  static int sort_functions(const void *a1, const void *a2);

private:
  CompileContext& cc_;
  sema::Program* program_;

  SmxAssemblyBuffer masm_;
  MemoryBuffer data_;

  SmxBuilder builder_;
  RefPtr<SmxNameTable> names_;

  struct FunctionEntry {
    Atom* name;
    ast::FunctionStatement* fun;

    FunctionEntry()
      : name(nullptr),
        fun(nullptr)
    {}
    FunctionEntry(Atom* name, ast::FunctionStatement* fun)
      : name(name),
        fun(fun)
    {}
  };
  ke::Vector<FunctionEntry> publics_;
};

} // namespace sp

#endif // _include_sourcepawn_emit_emitter_h_
