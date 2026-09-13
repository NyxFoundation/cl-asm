---
title: Whole-Routine Contract and Validation
last_updated: 2026-09-13
tags:
  - consensus
  - lean
  - riscv
  - verification
---

# Whole-Routine Contract and Validation

`ClAsm.Weigh.program` implements `weigh_justification_and_finalization` with
175 uncompressed RV64 instructions, including its return. It implements the
inner routine; the caller's first-two-epochs skip is not part of this operation.
`SLOTS_PER_EPOCH = 32` and `SLOTS_PER_HISTORICAL_ROOT = 8192` are fixed.

## ABI and memory

| Register | Input |
|---|---|
| `a0` / `x10` | State pointer, 136 bytes |
| `a1` / `x11` | 8192 opaque 32-byte roots, 262144 bytes |
| `a2` / `x12` | Total active balance |
| `a3` / `x13` | Previous target balance |
| `a4` / `x14` | Current target balance |
| `a5` / `x15` | Scratch pointer, 80 bytes |
| `ra` / `x1` | Return address outside the routine |

The state has a 64-bit slot at offset 0, a canonical four-bit field in a 64-bit
word at offset 8, and 40-byte previous/current/finalized checkpoints at offsets
16/56/96. A checkpoint contains a 64-bit epoch followed by four opaque root
words. Scratch holds the two original checkpoints at offsets 0 and 40.

The input registers and slot are preserved. Only `x5`, `x6`, `x7`, `x16`, `x17`,
`x28`, `x29`, `x30`, and `x31` are temporaries. The root array is preserved;
the frame rule covers the stack pointer, callee-saved registers, and other
disjoint caller-owned memory. State, roots, scratch, and code occupy disjoint
ranges without address overflow. Data accesses are valid aligned doublewords;
entry and return are four-byte aligned.

## Admitted arithmetic and state update

`ValidInput` requires the following bounds before word-level arithmetic:

- Bits are less than 16; both `3 * targetBalance` and `2 * totalBalance` fit uint64.
- Old previous epoch plus 3 and old current epoch plus 2 fit uint64.
- For each successful threshold, `start = epoch * 32` satisfies
  `start < slot <= start + 8192`, and `start + 8192` fits uint64.

There is no added `targetBalance <= totalBalance` condition. Epoch subtraction
saturates at genesis. The previous and current root accesses may coincide;
`rootsOwn_extract` borrows and reassembles one array element at a time.

Both original checkpoints are saved before previous is replaced by old current.
Bits shift left and are masked to four bits. Previous justification sets bit 1;
current justification sets bit 0 and wins if both update current. Four independent
finalization checks use the updated bits and saved checkpoints, in this order:

| Saved checkpoint | Epoch equality | Required bit mask |
|---|---|---|
| Old previous | old epoch + 3 = current epoch | 14 |
| Old previous | old epoch + 2 = current epoch | 6 |
| Old current | old epoch + 2 = current epoch | 7 |
| Old current | old epoch + 1 = current epoch | 3 |

Later successful checks overwrite earlier results. Root bytes never participate
in comparisons or arithmetic.

## Checked Lean claims

`Weigh.Proof.program_execution_spec` composes the prologue, both conditional
justifications, four conditional finalizations, final bit store, and return.
Each block is connected to a checked contiguous slice of the exact `Program`.
`Weigh.Meaning.executionResult_correct` identifies its word-level result with
the mathematical state transition. `Weigh.Correctness.program_spec` combines
these into the full frame-preserving bounded contract, with a limit of 175 steps.
This is a conservative static bound; measured paths use 99–147 steps.

`Weigh.Witness` constructs a complete inhabited call: code, all ABI registers,
136-byte state, all 8192 roots, 80-byte scratch, and an outside-code return.
`witness_pre`, `witness_addresses`, `witness_input`, `witness_code`, and
`witness_returns` check its premises and instantiate the whole-routine theorem.
The example uses zero checkpoints and roots, slot zero, total balance one, and
zero target balances. Region witnesses are proved inductively, without trusting
native proof evaluation.

## Official comparison and executable checks

The oracle extracts the unchanged function, its helpers, and declared types
from consensus-specs revision `530cf56a3920dc048900b4b7a408b3acd71331fa`.
`tests/vendor/reference.json` records the source and extracted SHA-256 hashes.
`scripts/extract_reference.py` checks the complete pinned source before extraction.
The adapter uses the real `eth-ssz-specs==0.1.0` integer, bitvector, container,
and root-vector types. Dependency versions are pinned in `tests/requirements.txt`.

The 4,796 admitted cases cover all bit patterns, both thresholds, equality and
nearby balances, zero and uint64 limits, old checkpoint relationships, each
finalization rule and competing overwrites, ring-buffer boundaries, genesis,
and deterministic random inputs. Out-of-contract range/time cases and malformed
input are rejected separately. The harness checks preserved registers and
initialized memory, both saved scratch checkpoints, successful return, and failure with one fewer than the
actually consumed steps. The seven helper probes add 1,747 cases.

The generator emits `weigh.program.json` from the proved instruction sequence.
An independent Python encoder assembles its raw instruction words separately,
compares all 700 executable bytes with `weigh.elf`, and checks ELF layout and
branch targets. Negative tests change an operand, corrupt metadata/returns,
inject public/private axioms, and exercise invalid executions and tool failures.

## Trust boundaries

The Lean theorem covers the pinned RV64 model and reference-condition
translation. Translation from official Python semantics is reviewed and tested,
not machine-proved. The emitter, GNU assembler/linker, ELF loader, byte checker,
and efficient interpreter state conversion are also tested boundaries.
The dependency's decoding-to-Sail and execution-state simulation gaps remain
as documented in [the bootstrap contract](bootstrap.md).

The axiom audit includes imported and private declarations and permits only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or compiler-trusting
proof axioms are accepted. ELF output is generated from proved model code and
validated by tests; it is not itself formally certified. zkVM integration and
individual execution proofs remain outside the v0 scope.
