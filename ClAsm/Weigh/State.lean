import ClAsm.Checkpoint
import ClAsm.EpochAtSlot

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

structure State where
  slot : Word
  bits : Word
  previous : Checkpoint
  current : Checkpoint
  finalized : Checkpoint
  deriving Repr, BEq, DecidableEq

structure Balances where
  total : Word
  previous : Word
  current : Word
  deriving Repr, BEq, DecidableEq

def State.owns (ptr : Word) (state : State) : Assertion :=
  (ptr ↦ₘ state.slot) ** (ptr + 8 ↦ₘ state.bits) **
    state.previous.owns (ptr + 16) ** state.current.owns (ptr + 56) **
    state.finalized.owns (ptr + 96)

def rootsOwn (base : Word) (roots : List Root) : Assertion :=
  match roots with
  | [] => empAssertion
  | root :: tail => root.owns base ** rootsOwn (base + 32) tail

def epoch (state : State) : Nat := state.slot.toNat / Layout.slotsPerEpoch
def previousEpoch (state : State) : Nat := epoch state - 1
def threshold (vote total : Word) : Bool := 3 * vote.toNat ≥ 2 * total.toNat
def rootIndex (epoch : Nat) : Nat := (epoch * Layout.slotsPerEpoch) % Layout.slotsPerHistoricalRoot

/-- These mathematical conditions preserve the reference's range-checked operations. -/
def rootTimeValid (state : State) (epoch : Nat) : Prop :=
  let start := epoch * Layout.slotsPerEpoch
  start < state.slot.toNat ∧ state.slot.toNat ≤ start + Layout.slotsPerHistoricalRoot ∧
    start + Layout.slotsPerHistoricalRoot < 2^64

structure ValidInput (state : State) (balances : Balances) : Prop where
  bits : state.bits.toNat < 16
  previousProduct : 3 * balances.previous.toNat < 2^64
  currentProduct : 3 * balances.current.toNat < 2^64
  totalProduct : 2 * balances.total.toNat < 2^64
  previousAddition : state.previous.epoch.toNat + 3 < 2^64
  currentAddition : state.current.epoch.toNat + 2 < 2^64
  previousRoot : threshold balances.previous balances.total = true → rootTimeValid state (previousEpoch state)
  currentRoot : threshold balances.current balances.total = true → rootTimeValid state (epoch state)

def finalizationHolds (bits : Word) (checkpoint : Checkpoint) (currentEpoch delta mask : Nat) : Bool :=
  bits.toNat &&& mask == mask && checkpoint.epoch.toNat + delta == currentEpoch

/-- Direct translation of the four independent conditions, in reference order. -/
def finalizedCheckpoint (state : State) (bits : Word) : Checkpoint :=
  let e := epoch state
  let f1 := if finalizationHolds bits state.previous e 3 14 then state.previous else state.finalized
  let f2 := if finalizationHolds bits state.previous e 2 6 then state.previous else f1
  let f3 := if finalizationHolds bits state.current e 2 7 then state.current else f2
  if finalizationHolds bits state.current e 1 3 then state.current else f3

/-- The whole-state postcondition; roots are an opaque caller-provided array. -/
def transition (state : State) (balances : Balances) (rootAt : Nat → Root) : State :=
  let prevOK := threshold balances.previous balances.total
  let currOK := threshold balances.current balances.total
  let bits := BitVec.ofNat 64 (((state.bits.toNat * 2) % 16) |||
    (if prevOK then 2 else 0) ||| (if currOK then 1 else 0))
  let current := if currOK then ⟨BitVec.ofNat 64 (epoch state), rootAt (rootIndex (epoch state))⟩
    else if prevOK then ⟨BitVec.ofNat 64 (previousEpoch state), rootAt (rootIndex (previousEpoch state))⟩
    else state.current
  { state with previous := state.current, current, bits, finalized := finalizedCheckpoint state bits }

end ClAsm.Weigh
