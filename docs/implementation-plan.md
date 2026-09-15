---
title: Implementation Completion Plan
last_updated: 2026-09-13
tags:
  - consensus
  - verification
  - benchmark
---

# Implementation Completion Plan

The objective is the complete v0 routine in `DESIGN.md`, plus reproducible
benchmarks. Helper proofs and passing helper tests alone do not complete it.

| Deliverable | Completion evidence | Current status |
|---|---|---|
| Arithmetic and copy macros | Bounded Lean triples, mathematical meanings, callable tests | Complete |
| Complete state and root-array contract | `Contract.lean`, `Witness.lean`; all 8192 roots and both scratch checkpoints | Complete |
| Whole routine | `Program.lean`; two ordered justifications, four ordered finalizations, return | Complete: 175 instructions / 700 bytes |
| Whole-routine proof | `Correctness.program_spec`; exact `Program`, preserved frame, bounded return | Complete: 175-step bound |
| ELF | Same ABI, independent byte and branch checks, GNU assembly, interpreter execution | Complete |
| Official differential tests | Pinned source and real SSZ types; 4,796 admitted cases and failure boundaries | Complete: all 19 Python tests pass |
| Negative checks and axiom audit | Imported/private declarations and deliberate corruption | Complete: 4,165 declarations, only three standard axioms |
| Benchmarks | Clean revision, ELF hash, raw batches, environment, separate RV64/host measurements | Complete: [results and reproduction](benchmarks.md) |
| Final review | Requirement audit, source build, tests, axiom audit, workflow lint | Complete locally; [PR #2 checks](https://github.com/NyxFoundation/cl-asm/pull/2/checks) gate delivery |

The [whole-routine contract](weigh.md) records the input mapping, preservation,
proof composition, inhabited witness, official-reference extraction, and trust
boundaries. The final benchmark must identify a clean source revision and ELF
hash, retain raw batch times, and separate modeled RV64 steps from host timing.
Cases outside the calling preconditions are reported separately from successful
differential cases. zkVM execution proofs and formal ELF correspondence remain
outside the approved v0 scope.
