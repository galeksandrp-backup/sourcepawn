// vim: set sts=2 ts=8 sw=2 tw=99 et:
// 
// Copyright (C) 2006-2015 AlliedModders LLC
// 
// This file is part of SourcePawn. SourcePawn is free software: you can
// redistribute it and/or modify it under the terms of the GNU General Public
// License as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// You should have received a copy of the GNU General Public License along with
// SourcePawn. If not, see http://www.gnu.org/licenses/.
//
#include "environment.h"
#include "linking.h"

using namespace sp;

#if defined(KE_LINUX)
#include <unistd.h>
#include <stdio.h>

// clock_gettime
#include <time.h>

// mmap
#include <sys/mman.h>

// creat
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

// __rdtsc
#include <x86intrin.h>

// When being used with Intel PT profiling, we need to use the CPU clock as our time source.
static bool use_arch_timestamp = false;

#define NSEC_PER_SEC 1000000000

static inline uint64_t get_perf_timestamp() {
  timespec ts;

  if (use_arch_timestamp) {
    return __rdtsc();
  }

  if (clock_gettime(CLOCK_MONOTONIC, &ts)) {
    return 0;
  }

  return ((uint64_t)ts.tv_sec * NSEC_PER_SEC) + ts.tv_nsec;
}

static uint16_t get_elf_machine() {
  uint16_t machine = 0; /* EM_NONE */

  FILE* exe = fopen("/proc/self/exe", "r");
  if (!exe) {
    return machine;
  }

  struct {
    uint8_t ident[16];
    uint16_t type;
    uint16_t machine;
  } __attribute__((packed)) elf_header;

  if (fread(&elf_header, sizeof(elf_header), 1, exe) != -1) {
    machine = elf_header.machine;
  }

  fclose(exe);
  return machine;
}

// Below structs cribbed from tools/perf/util/jitdump.h in the Linux source tree.

#define JITHEADER_MAGIC 0x4A695444
#define JITHEADER_VERSION 1

enum jitdump_flags_bits {
  JITDUMP_FLAGS_ARCH_TIMESTAMP_BIT,
  JITDUMP_FLAGS_MAX_BIT,
};

#define JITDUMP_FLAGS_ARCH_TIMESTAMP (1ULL << JITDUMP_FLAGS_ARCH_TIMESTAMP_BIT)

struct jitheader {
  uint32_t magic;      /* characters "jItD" */
  uint32_t version;    /* header version */
  uint32_t total_size; /* total size of header */
  uint32_t elf_mach;   /* elf mach target */
  uint32_t pad1;       /* reserved */
  uint32_t pid;        /* JIT process id */
  uint64_t timestamp;  /* timestamp */
  uint64_t flags;      /* flags */
};

enum jit_record_type {
  JIT_CODE_LOAD       = 0,
  JIT_CODE_MOVE       = 1,
  JIT_CODE_DEBUG_INFO = 2,
  JIT_CODE_CLOSE      = 3,
  JIT_CODE_MAX,
};

/* record prefix (mandatory in each record) */
struct jr_prefix {
  uint32_t id;
  uint32_t total_size;
  uint64_t timestamp;
};

struct jr_code_load {
  struct jr_prefix p;

  uint32_t pid;
  uint32_t tid;
  uint64_t vma;
  uint64_t code_addr;
  uint64_t code_size;
  uint64_t code_index;
  const char name[0];
  unsigned char bytes[0];
};

struct debug_entry {
  uint64_t addr;
  int lineno;
  int discrim;
  const char name[0];
};

struct jr_code_debug_info {
  struct jr_prefix p;

  uint64_t code_addr;
  uint64_t nr_entry;
  struct debug_entry entries[0];
};

static FILE* open_jitdump_file(pid_t pid) {
  char path[256];
  // We can keep this file anywhere, but the name must be ".../jit-XXXX.dump", where XXXX is our PID.
  // https://github.com/torvalds/linux/blob/614cb5894306cfa2c7d9b6168182876ff5948735/tools/perf/Documentation/jitdump-specification.txt
  ke::SafeSprintf(path, sizeof(path), "/tmp/jit-%d.dump", pid);

  int fd = open(path, O_CREAT|O_TRUNC|O_RDWR, 0666);
  if (fd < 0) {
    return nullptr;
  }

  // This mmap acts as a marker for perf to find our jitdump file.
  // The fd has to be opened before the file or perf can't find this mmap (i.e. fileno doesn't work).
  mmap(nullptr, sysconf(_SC_PAGESIZE), PROT_READ|PROT_EXEC, MAP_PRIVATE, fd, 0);

  FILE* file = fdopen(fd, "w+");
  if (!file) {
    close(fd);
    return nullptr;
  }

  // Use arch timestamps unless the env var is explicitly set to 0.
  char* env = getenv("JITDUMP_USE_ARCH_TIMESTAMP");
  use_arch_timestamp = !env || *env != '0';

  jitheader header = {};
  header.magic = JITHEADER_MAGIC;
  header.version = JITHEADER_VERSION;
  header.total_size = sizeof(header);
  header.elf_mach = get_elf_machine();
  header.pid = pid;
  header.timestamp = get_perf_timestamp();
  header.flags = use_arch_timestamp ? JITDUMP_FLAGS_ARCH_TIMESTAMP : 0;

  fwrite(&header, sizeof(header), 1, file);

  return file;
}
#endif

CodeChunk
sp::LinkCode(Environment* env, Assembler& masm, const char* name, const CodeDebugMap& mapping)
{
  if (masm.outOfMemory())
    return CodeChunk();

  auto length = masm.length();
  CodeChunk code = env->AllocateCode(length);

  auto address = code.address();
  if (!address)
    return code;

  masm.emitToExecutableMemory(address);

  // Some other debug info consumers we might want to implement here:
  //
  // * Intel VTune
  //   https://github.com/intel/ittapi
  //   Would give us profiling coverage on non-Linux.
  //   Very similar input (and use case) as perf, requires linking Intel code in though.
  //
  // * GDB JIT Interface
  //   https://sourceware.org/gdb/current/onlinedocs/gdb/JIT-Interface.html
  //   Lets GDB show JIT frames when debugging, with source info.
  //   Requires generating full ELF + DWARF objects in memory.

#if defined(KE_LINUX)
  static pid_t pid = getpid();

  static FILE* perf_jit_file = nullptr;
  static bool perf_jit_tried = false;
  if (!perf_jit_tried) {
    char perf_jit_path[256];
    // The specification requires the file to be located at exactly this path.
    // https://github.com/torvalds/linux/blob/614cb5894306cfa2c7d9b6168182876ff5948735/tools/perf/Documentation/jit-interface.txt
    ke::SafeSprintf(perf_jit_path, sizeof(perf_jit_path), "/tmp/perf-%d.map", pid);

    perf_jit_file = fopen(perf_jit_path, "w");
    perf_jit_tried = true;
  }

  if (perf_jit_file) {
    fprintf(perf_jit_file,
      (sizeof(long) == 8) ? "%lx %lx %s\n" : "%llx %llx %s\n",
      (uint64_t)address,
      (uint64_t)length,
      name);
  }

  static FILE* perf_jitdump_file = nullptr;
  static bool perf_jitdump_tried = false;
  if (!perf_jitdump_tried) {
    perf_jitdump_file = open_jitdump_file(pid);
    perf_jitdump_tried = true;
  }

  if (perf_jitdump_file) {
    if (!mapping.empty()) {
      jr_code_debug_info dbg_record = {};
      dbg_record.p.id = JIT_CODE_DEBUG_INFO;
      dbg_record.p.total_size = sizeof(dbg_record);
      dbg_record.p.timestamp = get_perf_timestamp();
      dbg_record.code_addr = (uintptr_t)address;
      dbg_record.nr_entry = mapping.size();

      for (const auto& map : mapping) {
        dbg_record.p.total_size += sizeof(debug_entry) + strlen(map.file) + 1;
      }

      fwrite(&dbg_record, sizeof(dbg_record), 1, perf_jitdump_file);

      for (const auto& map : mapping) {
        // Our special markers can be identified by them having a line number of 0,
        // perf doesn't like that so we just shift them up to 1 so they're not lost.
        debug_entry entry = {};
        entry.addr = (uintptr_t)address + map.addr;
        entry.lineno = map.line >= 1 ? map.line : 1;

        fwrite(&entry, sizeof(entry), 1, perf_jitdump_file);
        fwrite(map.file, 1, strlen(map.file) + 1, perf_jitdump_file);
      }
    }

    jr_code_load record = {};
    record.p.id = JIT_CODE_LOAD;
    record.p.total_size = sizeof(record) + strlen(name) + 1 + length;
    record.p.timestamp = get_perf_timestamp();
    record.pid = pid;
    record.tid = pid; // TODO: Use the thread id.
    record.vma = (uintptr_t)address;
    record.code_addr = record.vma;
    record.code_size = length;
    record.code_index = record.vma; // We don't re-JIT, so this should be fine.

    fwrite(&record, sizeof(record), 1, perf_jitdump_file);
    fwrite(name, 1, strlen(name) + 1, perf_jitdump_file);
    fwrite(address, 1, length, perf_jitdump_file);
  }
#endif

  return code;
}
