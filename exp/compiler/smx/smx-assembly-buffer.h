// vim: set sts=2 ts=8 sw=2 tw=99 et:
//
// Copyright (C) 2012-2014 AlliedModders LLC, David Anderson
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
#ifndef _include_spcomp_smx_assembly_buffer_h_
#define _include_spcomp_smx_assembly_buffer_h_

#include "assembly-buffer.h"
#include <smx/smx-v1-opcodes.h>
#include <sp_vm_types.h>

namespace sp {

class SmxAssemblyBuffer : public AssemblyBuffer
{
 public:
  SmxAssemblyBuffer()
  {}

  void opcode(OPCODE op) {
    write<cell_t>(static_cast<cell_t>(op));
  }
  void opcode(OPCODE op, cell_t param) {
    write<cell_t>(static_cast<cell_t>(op));
    write<cell_t>(param);
  }
  void opcode(OPCODE op, Label* address) {
    write<cell_t>(static_cast<cell_t>(op));
    encodeAbsoluteAddress(address);
  }

  void sysreq_n(Label* address, uint32_t nparams) {
    write<cell_t>(static_cast<cell_t>(OP_SYSREQ_N));
    encodeAbsoluteAddress(address);
    write<cell_t>(nparams);
  }

  void bind(Label* target) {
    bind_to(target, pc());
  }

  void bind_to(Label* target, cell_t value) {
    assert(value >= 0);

    if (outOfMemory()) {
      // If we ran out of memory, the code stream is potentially invalid and
      // we cannot use the embedded linked list.
      target->bind(0);
      return;
    }

    assert(!target->bound());
    uint32_t status = target->status();
    while (Label::More(status)) {
      uint32_t offset = Label::ToOffset(status);
      assert(offset >= 4 && offset <= pc());

      int32_t* p = reinterpret_cast<int32_t*>(buffer() + offset - 4);
      status = *p;
      *p = value;
    }
    target->bind(value);
  }

 private:
  void encodeAbsoluteAddress(Label* address) {
    if (address->bound()) {
      write<cell_t>(address->offset());
    } else {
      write<cell_t>(address->addPending(pc() + sizeof(cell_t)));
    }
  }

 private:
  // :TODO: assert labels bound
};

}

#endif // _include_spcomp_smx_assembly_buffer_h_
