---
title: Balance Aggregation Contract and Runner
last_updated: 2026-11-12
tags:
  - consensus
  - lean
  - riscv
  - testing
---

# Balance Aggregation Contract and Runner

`aggregate` computes the three balances supplied to
`weigh_justification_and_finalization`. It is a standalone 78-instruction
RV64 routine (312 bytes); it does not call or modify `weigh`.

For the pinned consensus-specs revision `530cf56`, it computes:

1. Total effective balance of validators active in the current epoch.
2. Previous-epoch effective balance of active, unslashed validators with the
   `TIMELY_TARGET` participation flag.
3. The same target balance for the current epoch.

Each result is floored at `EFFECTIVE_BALANCE_INCREMENT = 1,000,000,000`.
The current epoch is `slot / 32`; the previous epoch saturates at zero.
The Python functions in `tests/vendor/aggregate_balances.py` are the
hash-checked official reference, not a rewritten test oracle.

## Internal ABI

| Register | Input |
|---|---|
| `a0 / x10` | Validator-array base |
| `a1 / x11` | Previous-participation-array base |
| `a2 / x12` | Current-participation-array base |
| `a3 / x13` | Validator count |
| `a4 / x14` | Slot |
| `a5 / x15` | Three-word output area |
| `ra / x1` | Return address |

A validator occupies four little-endian uint64 words: effective balance at
offset 0, activation epoch at 8, exit epoch at 16, and slashed flag (0 or 1)
at 24. Each participation flag is a zero-extended uint8 stored in an
eight-byte word. These are internal layouts, **not SSZ serialization**.

The output words at offsets 0, 8, and 16 hold total, previous-target, and
current-target balances. Input arrays, slot, output base, return address,
and every register outside `temporaries` are preserved. The pointer
registers advance past the arrays and the counter becomes zero.
Only the three output words may change in memory.

The concrete runner uses:

| Region | Address |
|---|---|
| Code | `0x80000000` |
| Validators | `0xa0000000` |
| Previous flags | `0xa0100000` |
| Current flags | `0xa0200000` |
| Outputs | `0xa0300000` |

Capacity is 32,768 validators. All arrays must have the same length.
The runner rejects out-of-range integers, flags outside uint8, noncanonical
slashed values, and any of the three selected sums reaching `2^64`.
A large balance that contributes to none of the sums is allowed.

## Proof boundary

`ClAsm/Aggregate/Proof.lean:program_spec` proves the mathematical result,
input-resource preservation, preservation of disjoint caller-owned resources,
and return within `52 * N + 24` modeled steps. Its precondition owns all
read or written registers, binds `x14` to the input slot, and owns each
input and output memory cell. Address and input validity are explicit
hypotheses. `Witness.lean` constructs a satisfiable empty-array call and
derives its bounded return from that theorem.

`LoopProof.lean` proves the guarded loop by induction. Consumed cells stay
owned in the frame and are returned as the original arrays. The back jump
is `-208` bytes and lands on the guard, not its second instruction.
`Epilogue.lean` proves the three floor-and-store blocks and the return.

Assembly emission, linking, ELF loading, interpreter conversion, JSON
admission, and agreement with the official Python functions are tested,
not formally proved. The axiom audit includes these modules and accepts
only `propext`, `Quot.sound`, and `Classical.choice`.

## Run

First follow [the build and validation procedure](build.md). Then:

```sh
printf '%s\n' '{"slot":96,"validators":[{"effectiveBalance":32000000000,"activationEpoch":0,"exitEpoch":18446744073709551615,"slashed":0}],"previousFlags":[2],"currentFlags":[2]}' \
  | .lake/build/bin/cl-asm-aggregate build/aggregate.elf
```

The result has `total`, `previous`, and `current` equal to 32,000,000,000
and `steps` equal to 76. The runner accepts one JSON object per line and
returns one JSON result per line. It exits nonzero on invalid input or an
invalid image. Earlier successful lines can already have produced output.

Add `--benchmark 200 21` to measure 21 batches of 200 executions of the
same input. Each report includes the checked result, batch nanoseconds,
iteration count, and an observable checksum. Timing excludes ELF loading,
input preparation, JSON, and preservation checks; it includes interpreter
execution, one temporary-register reset, and checksum accumulation.

## Validation and cost

The differential suite covers 793 deterministic cases, all 256 flag
values, genesis and epoch boundaries, activation/exit boundaries, slashing,
the increment floor, uint64 sum limits, and randomized registries.
Separate tests cover the capacity boundary, malformed inputs, benchmark
parameters, independent instruction encoding, branch destinations, and
modified or truncated ELF images.

Observed execution follows `21 + 52 * N + e`, where `e` is the number
of raw sums at least the increment (`0 ≤ e ≤ 3`). The loop therefore costs
52 steps per validator in the local RV64 interpreter. The empty case takes
21 steps. No ZisK execution or proof-generation measurements for
`aggregate` are claimed; integrating it into a zkVM guest remains separate work.
