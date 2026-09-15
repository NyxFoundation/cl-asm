---
title: Bootstrap Contract and Validation
last_updated: 2026-09-13
tags:
  - lean
  - riscv
  - verification
---

# Bootstrap Contract and Validation

The foundation establishes the build, proof, code-generation, and execution
path for `epochAtSlot`. The [helper stage](helpers.md) extends that path to six
more callable probes. The [whole-routine contract](weigh.md) documents the
complete `weigh` implementation built on this foundation.

## Callable probe

`EpochAtSlot.program state dst` is the inline two-instruction helper: load the
64-bit slot at offset zero, then shift it right by five. `program_spec` exposes
the state-pointer register, destination register, and slot-cell ownership. Its
calling conditions require a nonzero destination and distinct registers.

`EpochAtSlot.callable` adds `jalr x0, 0(ra)`. This probe uses `a0` for the state
pointer and `t0` for the computed epoch; it preserves `a0`. It is named
`epoch_at_slot` in the ELF, independently of the `weigh` entry point. There is
no scalar-result convention added to the `weigh` ABI.

`callable_spec` proves a bounded Hoare triple tied to `CodeReq.ofProg` of that
exact `Program`. Its precondition owns `a0`, `t0`, `ra`, and the slot cell.
The slot must be accessible and doubleword-aligned as required by `memIs`.
The return address must have its low bit clear for JALR. The postcondition
preserves the pointer, input cell, and return register, and gives `t0` the epoch.
The built-in frame rule preserves other disjoint resources, including the
stack pointer, callee-saved registers, and all other memory. The step bound is
the actual length of the callable program: three.

`epoch_toNat` separately proves that the result is the mathematical unsigned
quotient `slot / 32`, for every 64-bit slot. `witness_pre`, `witness_code`,
`witness_return_outside`, and `witness_returns` provide an inhabited calling
example, including code placement and an observed return. Layout theorems
check region separation, extents, and alignment.

## Test memory map

| Region | Base | Size |
|---|---|---|
| Executable probe | `0x80000000` | 12 bytes |
| Return observation address | `0x80001000` | No instruction is executed here |
| State | `0xa0000000` | 136 bytes |
| Block roots | `0xa0010000` | 262144 bytes |
| Scratch | `0xa0050000` | 80 bytes |

The interpreter's model excludes the code window from data accesses. Data
regions are in its accepted RAM window. Entry and return addresses are
4-byte-aligned for the uncompressed RV64IM image; data regions are
8-byte-aligned and do not overlap.

The ELF contains one read-only executable load segment. The harness supplies
memory and registers, checks for return before the next fetch, and never uses
ECALL or a zkVM exit protocol. The root array and scratch are populated with
sentinels so unintended writes are visible. These fixtures exercise the helper;
they are not claimed to satisfy the full `weigh` preconditions.

## Validation and trust boundaries

The emitter consumes the same `Program` used in the proof and supports only
the real instruction forms needed by this increment. Unsupported instructions
fail explicitly. Assembly-format tests cover the forms, signed offsets, and
shift limits. The ELF's entry, segment address, extent, permissions, and bytes
are checked. The expected 12 bytes are fixed independently of the emitter, and
the loaded decoded instructions are also compared with the `Program`.

The interpreter executes the image for boundary and deterministic sample
inputs. Negative tests deliberately corrupt metadata, instruction bytes, and
modeled executions so that the checks must reject errors. These tests do not
constitute an ELF-to-model proof. This helper uses mathematical integer division
as its independently evaluated expected result; the [full routine](weigh.md)
has separate official Python differential tests.

`scripts/CheckAxioms.lean` checks compiled declarations in the project and the
imported RV64 model, logic, and interpreter namespaces. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Any additional axiom, including
`sorryAx` or compiler-trusting proof axioms, fails the check. No Sail equivalence
modules are imported by this increment.

The dependency is pinned to `riscv-zkvm`
`afcbc45e1c74c2d296e032b5606dd977a304e8ad`, with its pinned `lean-sail` dependency.
Its [documented proof gaps](https://github.com/Verified-zkEVM/riscv-zkvm/blob/afcbc45e1c74c2d296e032b5606dd977a304e8ad/docs/validation.md)
remain relevant: decoding-to-Sail correspondence and the efficient execution
state's simulation are not proved. The emitter, GNU assembler/linker, ELF
loader, and consistency checks also remain outside the formal proof.

## Whole routine

The helper stage now supplies checkpoint/root ownership, arithmetic macros,
root addressing, copying, bounded callable proofs, and ELF tests. These are
composed into the [complete `weigh` contract](weigh.md), including the state,
root-array ownership, arithmetic conditions, and ordered conditional updates.
