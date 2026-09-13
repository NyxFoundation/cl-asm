---
title: Helper Contracts and Validation
last_updated: 2026-09-13
tags:
  - consensus
  - lean
  - riscv
  - verification
---

# Helper Contracts and Validation

This stage implements the arithmetic and memory-copy building blocks for
`weigh_justification_and_finalization`. All seven probes have bounded,
frame-aware Lean contracts for their exact modeled `Program`, including the
return through `ra`. They share the bootstrap memory map and use separate ELF
images at the same entry address.

## Implemented contracts

| Helper | Behavior | Inline steps | Callable steps |
|---|---|---:|---:|
| `epochAtSlot` | Load slot and compute unsigned `slot / 32` | 2 | 3 |
| `previousEpoch` | Compute `max(epoch - 1, 0)` | 3 | 4 |
| `shiftJustificationBits` | Compute `(bits * 2) mod 16` | 2 | 3 |
| `hasSupermajority` | Produce 0 or 1 for `3 * vote >= 2 * total` | 5 | 6 |
| `blockRootAddress` | Compute `roots + ((epoch * 32) mod 8192) * 32` | 3 | 4 |
| `copyCheckpoint` | Copy the epoch and all 32 root bytes | 10 | 11 |
| `copyRoot` | Copy all 32 root bytes | 8 | 9 |

`ClAsm/Arithmetic/Proof.lean` proves the inline instruction contracts;
`Meaning.lean` connects their word results to mathematical natural numbers.
Previous epoch saturates at genesis without adding an early return. The bit
operation also has a proved meaning for noncanonical inputs, although the
complete `weigh` contract will still require the specified four-bit input.

The supermajority meaning theorem requires `3 * vote < 2^64` and
`2 * total < 2^64`. It preserves both input registers and uses two temporary
registers. It does not assume `vote <= total`. The instruction contract itself
describes 64-bit arithmetic; the natural-number interpretation is guaranteed
under the two stated bounds.

Root addressing masks the epoch to eight bits before shifting by ten:
`(epoch mod 256) * 1024`. The offset theorem proves equivalence to the mainnet
formula, 8-byte alignment, and containment of the entire 32-byte root within
the 262144-byte array. Pointer addition uses word arithmetic. A caller must
provide a valid nonwrapping region; this helper does not validate the temporal
conditions of `get_block_root` or own/read the array. `copyRoot` separately
provides the selected root's memory-read and copy contract.

`Root.owns` and `Checkpoint.owns` describe four and five aligned doubleword
cells, respectively. `copyRoot_spec` and `copyCheckpoint_spec` require source
and destination ownership in separating conjunction, so the regions are
disjoint. They preserve source data and both pointers, write exactly the
destination, and leave the temporary register holding the final copied word.
All other disjoint resources are preserved through the frame rule. These are
fixed-size copies, not overlapping-memory move operations.

`ClAsm/Probes/Proof.lean` composes each body contract with the return instruction.
The caller owns `ra` and supplies a return address with its low bit clear.
Step bounds are the actual program lengths. The original epoch probe retains
its concrete calling witness, code-placement proof, and outside-code return
witness in `ClAsm/EpochAtSlot/Witness.lean`.

## Executable validation

`cl-asm <directory>` generates all seven images. `cl-asm-test <directory>`
validates and executes the entire suite; `cl-asm-test <probe-name> <elf-path>`
checks one image. Probe names and independent literal instruction encodings
are in `ClAsm/Probes.lean`. Every image is checked for entry address, one RX
load segment, exact extent, exact instruction bytes, and decoded instructions
matching the modeled program.

| Probe | Cases |
|---|---:|
| Epoch at slot | 149 |
| Previous epoch | 149 |
| Justification bits | 181 |
| Supermajority | 316 |
| Block-root address | 662 |
| Checkpoint copy | 32 |
| Root copy | 258 |
| Total | 1747 |

Expected arithmetic uses unbounded natural numbers independently of the word
implementations. Threshold fixtures include zero, equality, adjacent values,
maximum admitted products, and votes exceeding total. All successful threshold
fixtures satisfy both multiplication bounds. Root cases include consecutive
epochs around multiple wraparounds. Copy cases use distinct words and both
state and scratch destinations; initialized state, root-array, and scratch
memory are compared in full after execution.

Every case checks outputs, preserved registers, memory, host state, and return;
one fewer unit of fuel must fail. Deliberate modeled mutations cover wrong
arithmetic, clobbered registers, invalid loads, nontermination, and a store
outside the destination. Python tests reject corrupted ELF metadata, changed
operands, a corrupted return in every probe, and assembler failure.

The axiom audit covers all new proofs and their imported RV64 dependencies,
including private declarations recovered from Lean's internal name prefix.
Negative tests inject unused public and private axioms and require rejection.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. ELF generation
and interpreter conversion retain the [bootstrap trust boundaries](bootstrap.md).

## Whole routine

The [complete `weigh` contract](weigh.md) composes these helpers with both
justification updates and all four finalization checks. It includes the state
and root-array ownership, arithmetic and temporal preconditions, a bounded
return proof, a concrete calling witness, and official Python differential tests.
