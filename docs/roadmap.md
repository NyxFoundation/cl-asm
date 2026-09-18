---
title: Purpose and Roadmap for Proving the Consensus Layer
last_updated: 2026-09-18
tags:
  - consensus
  - zkvm
  - roadmap
---

# Purpose and Roadmap for Proving the Consensus Layer

This document records why `weigh_justification_and_finalization` was chosen,
where it sits in the beacon chain's state transition, what the 2026-09-17
ZisK measurements established, which decisions were taken for the PoC, and
which parts of the consensus layer remain candidates for zkVM proving as
Ethereum moves to a proven execution layer and hash-based signatures. It is a
statement of direction, not a specification; the contracts and measurements
it cites live in [the whole-routine contract](weigh.md) and
[the benchmark record](benchmarks.md).

## 1. Why prove the consensus-layer state transition

Every beacon node runs `state_transition` for every block, and `process_epoch`
once per epoch (every 32 slots, 6.4 minutes). Correctness today rests on
several independent client implementations reaching the same result; a
participant that cannot run a node (a light client, a bridge, a rollup
contract) cannot check that result and instead trusts a sync committee's
signatures. Proving the state transition in a zkVM replaces "every node
re-executes" with "one prover executes, everyone verifies a proof", and it
makes the verified claim "the specification's transition" rather than "what
client X computed", provided the proved program is itself shown equivalent to
the specification. That is the role of the Lean proof in this repository: the
zkVM proves that the 175-instruction program ran, and Lean proves that this
program implements the specified transition, so neither trust assumption
depends on a client implementation.

`weigh_justification_and_finalization` is the first target because it is the
consensus conclusion (which checkpoint is final) while containing no hashing
and no signature checks, so the whole pipeline (Lean contract, ELF emission,
byte checking, official-reference differential tests, zkVM execution and
proof) can be exercised end to end on a 700-byte program.

## 2. Where the routine sits

```
EL client ──ExecutionPayload──► proposer ──BeaconBlock──► every CL node
                                                            │ engine_newPayload → VALID
                                                            │ process_slots
                                                            │   process_slot: block_roots[slot % 8192] = previous block root
                                                            │ process_block
                                                            │   process_execution_payload
                                                            │   process_attestation: participation flags (TIMELY_TARGET)
validators ──AttestationData{source, target}──► aggregators ─┘   (BLS signatures verified here, before this point)
                                                            │
                                            epoch boundary (slot % 32 == 0)
                                                            │ process_epoch
                                                            │   process_justification_and_finalization
                                                            │     total/previous-target/current-target balances
                                                            │       aggregated from participation flags
                                                            │     weigh_justification_and_finalization(state, total, prev, cur)   ◄── this repository
                                                            │   rewards, penalties, registry, slashings, effective balances, ...
```

The routine receives three balances and the state, reads two entries of
`block_roots`, and writes `justification_bits`, the two justified checkpoints,
and `finalized_checkpoint`. Signature verification happens earlier in
`process_attestation` and at block entry; balance aggregation happens in the
caller. The routine itself performs no cryptography: roots are copied as
opaque 32-byte values.

## 3. What the zkVM measurements established

The [ZisK measurements](benchmarks.md#zisk-zkvm-measurements) on an RTX 5090
gave, per scenario, 99–147 ZisK steps for `weigh` (equal to the modeled RV64
step counts), about 74,400 steps for the guest wrapper that materializes the
8192-entry root array, and 1.8–2.0 s of GPU proof generation that does not
vary with the scenario. ZisK proves fixed 2^22-row trace tables per segment;
this workload fills under 2% of the main table, so 97.6% of ZisK's own cost
model is the fixed base cost of one segment. Consequences:

- Instruction-count reductions in `weigh` cannot change proof time until a
  workload exceeds one segment. The figure to track is steps by symbol, not
  wall time.
- Per-process overheads (about 6.7 s of proving-key loading, a one-time GPU
  cache build) dominate the measured wall time. They are deployment costs, to
  be removed by a resident prover, not properties of the routine.
- Meaningful cost measurement starts when loops over validators enter the
  guest. The wrapper's root initialization is already 500 times the routine.

## 4. Decisions for the PoC

| Decision | Choice | Reason |
|---|---|---|
| State access model | Follow the beacon spec's in-memory `BeaconState`: pass all 8192 roots as input | The PoC conforms to the spec as written. Stateless access with SSZ Merkle proofs is recorded in [issue #4](https://github.com/NyxFoundation/cl-asm/issues/4) for later |
| Headline metric | `weigh` steps by symbol and ZisK's internal proof-generation time; wall time, key loading, and setup reported as separate overheads | The user's criterion is practical usability of the whole STF; one-time and per-process costs do not bear on it |
| Resident prover | Future work | ZisK ships coordinator and worker binaries; not needed to judge the routine |
| GPU re-measurement | Not repeated for this revision | The guest built from the repository is byte-identical in every code and data section to the one measured on 2026-09-16 |

## 5. Remaining consensus-layer work for a zkVM

Ordered by distance from the current tooling and by cost driver.

**Epoch processing without cryptography.** Same method as `weigh`; loops over
the validator set are the cost driver and give the first per-validator step
figures.

| Function | Content |
|---|---|
| balance aggregation in `process_justification_and_finalization` | `get_total_active_balance`, previous and current target balances from participation flags; the direct caller of `weigh` |
| `process_inactivity_updates` | inactivity scores |
| `process_rewards_and_penalties` | rewards and penalties from participation flags |
| `process_registry_updates` | activation and exit queues |
| `process_slashings` | slashing penalties |
| `process_effective_balance_updates` | effective-balance hysteresis |
| participation and randao buffer rotations | array copies |

**Block processing without signatures.** `process_block_header`, the
non-signature checks of `process_attestation` and its participation-flag
updates, `process_execution_payload` header consistency, withdrawals, and the
Electra request types.

**Cryptography.** SSZ `hash_tree_root` for `state_roots` and `block_roots`
(SHA-256; a precompile exists in ZisK; whole-state hashing needs incremental
update), and BLS12-381 aggregate signature verification (no ZisK precompile
today; impractical in general RV64 instructions).

**Outside the state transition.** Fork choice, networking, and signature
generation are node decisions, not transitions, and are not proved.

## 6. The lean Ethereum setting

The lean Ethereum direction changes two of the items above. The execution
layer is proved by a zkEVM and the consensus client verifies that proof
instead of executing the payload. BLS is replaced by hash-based XMSS
signatures whose verification is aggregated by proving it in a minimal zkVM
(leanVM), so the consensus client verifies an aggregate proof instead of
pairings. After both changes, the computation an attester still performs
unproven is the consensus-layer state transition itself.

```
EL client ──ExecutionWitness──► zkEVM guest ──► prover ──► zkEVM proof ─────┐
validators ──XMSS signatures──► leanVM (signature verification) ──► aggregate proof ─┤
                                                                            ▼
                     CL STF guest (this repository's method) ──► CL STF proof ──► zkAttester, light clients
                       · recursively verifies the zkEVM proof
                       · recursively verifies the aggregate signature proof
                       · counts votes, justifies, finalizes, updates the validator set
                       · recomputes the state root (hash-based SSZ)
```

What remains for a consensus-layer zkVM in that setting:

- The state-transition logic: slot processing, header checks, vote counting,
  justification and finalization (3-slot finality in lean consensus rather than
  Casper FFG), validator entry, exit, and balance updates. This is the
  continuation of `weigh`; the structure "count weighted votes, justify,
  finalize" carries over even though the rules change.
- Recursive verification of the zkEVM proof and the signature-aggregation
  proof inside the CL guest, folding execution, signatures, and consensus into
  one proof that an attester verifies once.
- State-root computation with hash-based commitments, which fits a zkVM with
  a hash precompile far better than pairing-based cryptography did.
- Stateless state access with Merkle proofs (issue #4), worth revisiting once
  the hash function is the one the lean design settles on.

Removing BLS from the consensus layer removes the largest obstacle to proving
it: what is left is logic plus hashing, the shape this repository's method
already handles.

## 7. Recommended next steps

1. Bring the balance aggregation of `process_justification_and_finalization`
   into the guest and record steps per validator; this is the first measurement
   that speaks to practical cost.
2. In parallel, check that the Lean-contract-to-ELF method applies to the lean
   consensus (3SF) state transition, whose specification is small. The future
   consensus-layer zkVM target is that transition, and confirming the tooling
   fits it early is the highest-value check available now.
3. Defer hashing and stateless access (issue #4) until the hash function is
   fixed; defer a resident prover until proof latency, not routine cost, is the
   question.
