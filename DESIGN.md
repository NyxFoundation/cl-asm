# CL ASM v0 — Design Proposal

Last updated: 2026-09-13. This document records the v0 design. The first implementation increment covers the `epochAtSlot` helper, its Lean proofs, and an executable ELF probe; see [Bootstrap Contract and Validation](docs/bootstrap.md). The complete `weigh` routine is not implemented yet.

## 1. Agreed Scope

- Implement the design in staged, independently validated increments.
- The initial target is `weigh_justification_and_finalization` and the small helpers needed to implement it.
- Treat each operation as a combination of a RISC-V instruction sequence, a memory representation, preconditions and postconditions, and a proof.
- Do not require a separate CL specification repository or a second Lean implementation of the entire consensus layer.
- Expose an internal memory interface to the required state fields. Leave SSZ decoding and vote-balance aggregation to the caller.
- Under explicit calling preconditions, guarantee correct results, preservation of memory outside the modification footprint, and termination for the instruction sequences in the machine model. The initial version does not guarantee that the internal routine itself detects precondition violations.
- Future composition must also prove that callers establish these preconditions.
- Fix the initial image to the mainnet preset constants: `SLOTS_PER_EPOCH = 32` and `SLOTS_PER_HISTORICAL_ROOT = 8192`.
- Limit the initial deliverables to ELF output. Integration with a specific zkVM, zkVM-specific input/output and startup/shutdown handling, and generation or verification of execution proofs are out of scope.
- Use the Lean-based RISC-V interpreter from `riscv-zkvm` to test the generated ELF. This is a validation tool, not integration with an actual zkVM.
- Limit formal verification in Lean to the instruction sequences. Validate ELF generation and consistency through tests; the initial version does not include formal proofs of the emitter, assembler, linker, ELF loader, or consistency checker, or a formal proof connecting the ELF to the instruction sequences.

The ABI, layout, and component breakdown below are proposals that make this scope concrete. Remaining design decisions are listed at the end.

## 2. References and Meaning of the Proofs

The reference function and accessors come from the [Phase0 specification at consensus-specs `530cf56a3920dc048900b4b7a408b3acd71331fa`](https://github.com/ethereum/consensus-specs/blob/530cf56a3920dc048900b4b7a408b3acd71331fa/specs/phase0/beacon-chain.md#justification-and-finalization). Referencing this function does not imply implementing all of Phase0 or the entire current consensus layer.

This revision obtains its integer types from `eth-ssz-specs==0.1.0`. `Gwei` and `Epoch` derive from `Uint64`, and the results of addition and multiplication are also range-checked. See the [dependency declaration](https://github.com/ethereum/consensus-specs/blob/530cf56a3920dc048900b4b7a408b3acd71331fa/pyproject.toml) and [integer type implementation](https://github.com/ethereum/ssz-specs/blob/7bce07ff7d51b1a3c66ff4e2bd3233ac248ede70/src/ssz/uint.py).

The Lean proofs establish that the instruction sequences satisfy this routine's state-update conditions. The correspondence between the official Python operation semantics and the Lean conditions is not claimed to be machine-proved. Validate that translation through a mapping to the reference source, review of the conditions, and comparison tests against the official routine.

Likewise, conversion from the proved instruction sequences to an executable ELF is a trust boundary checked through tests. Describe the artifact as an "ELF generated from instruction sequences proved in the model and validated through tests," not as an "ELF whose correctness is formally proved."

The machine model and separation logic from the investigated `riscv-zkvm v0.3.0` (`afcbc45e1c74c2d296e032b5606dd977a304e8ad`) are candidates for reuse. The evm-asm investigation is pinned to `7e65e4d024718f704226cd795f3d03d4e9aafe13`. Assess the impact on theorems and the execution environment before updating dependencies.

## 3. Proposed Internal Memory Layout and Calling Convention

Expose `weigh` as a single callable RISC-V routine, with its small internal components expanded inline as Lean macros.

| Argument register | Contents |
|---|---|
| `a0` / `x10` | Base address of the state region |
| `a1` / `x11` | Base address of the read-only `block_roots` array |
| `a2` / `x12` | Total effective balance `T` |
| `a3` / `x13` | Previous-epoch voting balance `A_prev` |
| `a4` / `x14` | Current-epoch voting balance `A_curr` |
| `a5` / `x15` | Base address of caller-provided scratch memory |

Return results by updating the state in place; there is no scalar return value. The routine makes no internal subroutine calls and returns to `ra` at the end. Preserve `sp` and callee-saved registers. List the caller-saved registers used by the routine as scratch resources in its contract.

### State Region: 136 Bytes

| Offset | Size | Field |
|---|---:|---|
| `0` | 8 | `slot` |
| `8` | 8 | `justification_bits` (low four bits used; upper bits zero) |
| `16` | 40 | `previous_justified_checkpoint` |
| `56` | 40 | `current_justified_checkpoint` |
| `96` | 40 | `finalized_checkpoint` |

Each checkpoint consists of an 8-byte epoch and a 32-byte root. Integers are little-endian, and roots are stored as sequences of 32 bytes. This is an internal ABI layout, not the SSZ layout of the full BeaconState.

`block_roots` occupies a separate region of `32*N` bytes containing `N = SLOTS_PER_HISTORICAL_ROOT` roots. Allocate 80 bytes of scratch memory to save the old previous and current checkpoints, 40 bytes each. The state region, root array, and scratch region must be pairwise disjoint and 8-byte aligned.

Preserve `slot` and the root array. The initial contents of scratch memory are arbitrary, and the caller must not attach meaning to its final contents. This routine includes no heap allocation, cryptographic operations, or host calls.

## 4. Calling Preconditions

Use the mainnet preset for the initial image, fixing `S = SLOTS_PER_EPOCH = 32` and `N = SLOTS_PER_HISTORICAL_ROOT = 8192` at build time. See the [mainnet constants at the pinned revision](https://github.com/ethereum/consensus-specs/blob/530cf56a3920dc048900b4b7a408b3acd71331fa/presets/mainnet/phase0.yaml).

The root array occupies `32*8192 = 262144` bytes (256 KiB). The routine reads at most two required roots rather than traversing the entire array. Support for the minimal preset is not a requirement for the initial image. Adopting mainnet constants does not imply support for the entire consensus layer or the mainnet execution environment.

Define the following in terms of the values represented in memory:

- `E = floor(slot / S)`.
- `P = max(E - 1, 0)`. Match the official accessor's treatment of the previous epoch at genesis.
- `prevOK` is the mathematical integer comparison `3*A_prev >= 2*T`.
- `currOK` is the mathematical integer comparison `3*A_curr >= 2*T`.

The contract requires the following preconditions:

1. All specified regions are accessible in the machine model, and address calculations do not wrap around. The code region is not overwritten as data.
2. Input integers fit within 64 bits, and justification bits use a canonical four-bit representation.
3. `3*A_prev`, `3*A_curr`, and `2*T` are each less than `2^64`.
4. Adding 3 to the old previous checkpoint's epoch and 2 to the old current checkpoint's epoch stays within the 64-bit range. This is a sufficient condition for the initial proof, not a claim to cover every successful input of the official function.
5. If `prevOK`, let `k=P*S` and require `k < slot <= k+N`. If `currOK`, require the same condition with `k=E*S`. Intermediate values needed to evaluate the official accessors must also stay within their integer types' ranges.
6. The entry address, return address, modeled code layout, and register ownership conditions are valid. The return address lies outside the routine and satisfies the required instruction alignment.

Do not add a precondition that voting balances must be no greater than the total effective balance. The outer layer is responsible for ensuring that the supplied balances were aggregated correctly; this routine processes those aggregation results as arguments.

The initial `hasSupermajority` example was a proposal for computing the mathematical threshold comparison over all 64-bit inputs. When relating it to the CL routine, show agreement with the official operation results within the ranges above. Do not claim that the example implements Python's exception behavior outside those ranges.

## 5. Execution Order and Component Breakdown

```text
Save the old checkpoints
          ↓
Compute E and P from slot
          ↓
Set the previous checkpoint to the old current checkpoint; shift bits
          ↓
Check the previous-epoch threshold → if met, read the root and update current and bit 1
          ↓
Check the current-epoch threshold → if met, read the root and update current and bit 0
          ↓
Evaluate and apply the four finalization conditions in specification order
          ↓
Return to the caller
```

| Macro / operation | Property to prove |
|---|---|
| `copyCheckpoint` | Copy the 40 bytes of the epoch and root while preserving other regions |
| `epochAtSlot` | Compute the quotient by the positive constant `S` |
| `previousEpoch` | Compute `max(E-1, 0)` |
| `hasSupermajority` | Produce 0 or 1, matching the threshold comparison |
| `blockRootAtEpoch` | Read `block_roots[(epoch*S) mod N]` under the time-range preconditions |
| `shiftJustificationBits` | Correctly shift and truncate the low four bits |
| Each justification branch | Update the corresponding checkpoint and bit |
| Each finalization branch | Perform a conditional update using an old checkpoint |
| Overall composition | Connect the final state, region preservation, and termination guarantees |

Pass the registers used by each macro explicitly, and include its read and clobber sets in the contract. The earlier `hasSupermajority` example used `x10` as its result register, so it cannot be concatenated unchanged into this ABI, which stores the state pointer in `x10`. Design the register assignment and any necessary saves, and prove the composition. Building a general-purpose register-allocating compiler is out of scope.

Unroll small fixed-size copies. The initial routine does not require data-dependent loops. Derive the step bound from the generated instruction sequences and the bounds of their branches rather than choosing a guessed constant. Evaluate RISC-V step counts separately from the proving cost of any particular zkVM.

## 6. Overall Postconditions

Let `oldPrev`, `oldCurr`, `oldFinal`, and `oldBits` denote the input values.

- `previous' = oldCurr`.
- `bits' = ((oldBits << 1) & 15) | (prevOK ? 2 : 0) | (currOK ? 1 : 0)`.
- `current'` is `(E, root(E))` if `currOK`; otherwise `(P, root(P))` if `prevOK`; otherwise `oldCurr`.
- `finalized'` is the result of applying the following four conditions in order. If none holds, it remains `oldFinal`.

| Order | Condition (using `bits'`) | Updated value |
|---|---|---|
| 1 | `(bits' & 14) = 14` and `oldPrev.epoch + 3 = E` | `oldPrev` |
| 2 | `(bits' & 6) = 6` and `oldPrev.epoch + 2 = E` | `oldPrev` |
| 3 | `(bits' & 7) = 7` and `oldCurr.epoch + 2 = E` | `oldCurr` |
| 4 | `(bits' & 3) = 3` and `oldCurr.epoch + 1 = E` | `oldCurr` |

Writes from later satisfied conditions take precedence. Do not replace these checks with an `else-if` chain or use the updated current checkpoint for finalization without justification.

The official logic that skips the first two epochs belongs to the outer `process_justification_and_finalization` routine. Do not add a new early return to this `weigh` routine.

Preserve all memory except the four updated fields and scratch memory. Express this using the frame rule of separation logic. Do not state only the result while omitting ownership conditions for the resources being modified.

## 7. ELF Output and Trust Boundaries

The initial version covers proofs of the instruction sequences, ELF output, and testing that ELF with the Lean-based RISC-V interpreter. Check conversion from instruction sequences to ELF, layout, and loading through tests rather than formal proofs. Support for general-purpose OS applications or a specific zkVM's guest SDK is out of scope.

The routine in the ELF retains the internal ABI from Section 3. A test harness is responsible for preparing the input state and initial registers, observing the return, and reading the results. Do not add SSZ input/output or zkVM-specific host calls to the CL routine itself. Finalize the harness interface together with the ELF layout and entry-point design.

### Scope of Formal Proofs

Prove a bounded Hoare triple in Lean for a fixed `Program` and a concrete calling contract. Compose the proofs to cover the results, resource preservation, and return of the entire modeled `weigh` routine, not just its small macros.

### Scope of Testing

The output path is `Program → assembly text → existing GNU assembler and linker → ELF`, following the approach in [evm-asm's output driver](https://github.com/Verified-zkEVM/evm-asm/blob/7e65e4d024718f704226cd795f3d03d4e9aafe13/EvmAsm/Codegen/Driver.lean).

- Test that each instruction form used emits the expected assembly text.
- Compare the target routine's bytes in the linked ELF against bytes separately emitted and assembled from the `Program` used in the proof. Also check the addresses used for comparison, including layout, entry point, and branch targets, against the link results.
- Run the generated ELF with the Lean-based RISC-V interpreter and compare its results with the official Python implementation on the same inputs.

The byte comparison is a test similar to [evm-asm's consistency-checking script](https://github.com/Verified-zkEVM/evm-asm/blob/7e65e4d024718f704226cd795f3d03d4e9aafe13/scripts/check-guest-image-program-bytes.py); do not require a Lean proof of the checker's correctness. A comparison that uses the same emitter and assembler on both sides may miss conversion bugs shared by both paths. Combine it with output-format tests and execution-result comparisons, but do not describe these as formal proofs.

### Components Not Proved in the Initial Version

Record the emitter, assembler, linker, ELF loader, and byte-comparison checker as trust boundaries for claims about the executable ELF. Formal proofs of these components, or of the correspondence between an individual ELF and the modeled instruction sequences, are not initial completion criteria. evm-asm also deliberately excludes code generation from its formal verification scope. See [evm-asm's trust boundaries](https://github.com/Verified-zkEVM/evm-asm/blob/7e65e4d024718f704226cd795f3d03d4e9aafe13/DRIFT.md#trust-boundaries-unverified-by-design).

The investigated `riscv-zkvm` revision provides instruction-level correspondence and execution simulation under specific assumptions. However, gaps remain in areas such as the correspondence between the byte decoder and Sail, and the executable memory representation. See the [validation scope of the investigated revision](https://github.com/Verified-zkEVM/riscv-zkvm/blob/afcbc45e1c74c2d296e032b5606dd977a304e8ad/docs/validation.md).

Document these interpreter-side proof gaps, but do not require closing them for the initial version. The concrete ELF layout, entry point, and loading and return-observation methods for tests remain design work.

A Lean proof of instruction-sequence correctness is distinct from a zkVM proof of an individual execution. The latter is not an initial completion criterion.

## 8. Initial Validation Plan

- Check the theorems for every macro and the full routine in Lean. Do not call the work complete while leaving unproved component contracts as assumptions of the top-level theorem.
- Construct a concrete witness that satisfies the initial-state preconditions, including instruction placement, region separation, and the return address, to avoid vacuous preconditions.
- Record the axioms used, including those from dependencies. The absence of `sorry` alone is not a sufficient completion criterion for correctness.
- Run the output-format, byte-comparison, and layout checks from Section 7. Introduce deliberate mismatches and confirm that the checks fail. A formal proof of the checker itself is not required.
- Cover all four-bit input patterns, combinations of the two threshold outcomes, values just below, at, and above the thresholds, and each finalization condition.
- Use distinct checkpoint roots to check preservation of old values and overwrites by later conditions.
- Check root-array index wraparound, time-range boundaries, and the boundaries of the explicit integer ranges.
- Compare the instruction sequence / executable image results against the pinned official Python function on the same inputs.
- Load the generated ELF with the Lean-based RISC-V interpreter, and have the test harness supply inputs through the same internal ABI and read the results. This tests the ELF's behavior; check the modeled instruction-sequence proofs separately. A proof connecting the ELF to the model is not required for the initial version.
- When reusing official epoch-processing tests, account for the fact that they also cover outer operations such as balance aggregation. Extract the arguments and state at the call to `weigh` so that the comparison targets match.
- Record discrepancies on inputs outside the preconditions as outside the guarantee; do not include them in successful-case statistics.

The initial version is complete when the modeled routine's proofs check in Lean, ELF generation works, the output, consistency, and behavioral comparison tests above pass, and the proof scope and trust boundaries are documented. The absence of a formal ELF-correspondence proof or zkVM execution proofs does not make the initial version incomplete.

## 9. Remaining Design Work

1. **ELF layout, entry point, and test harness.** Specify how to supply inputs through the internal ABI from Section 3 and observe the routine's return and results. Validate these through tests; do not add formal proofs of the loader or similar components.
2. **Implementation order and stage deliverables.** Organize contracts, small macros, full composition, ELF output, and comparison tests by dependency order, and assign the completion criteria from Section 8 to those stages.

The first increment's concrete layout, return observation, deliverables, and validation are recorded in [Bootstrap Contract and Validation](docs/bootstrap.md). Extend that foundation to the complete `weigh` routine in subsequent increments.
