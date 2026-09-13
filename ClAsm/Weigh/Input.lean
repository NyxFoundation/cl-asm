import ClAsm.Weigh.State
import Lean.Data.Json

namespace ClAsm.Weigh.Input

open Lean RiscvZkvm.Rv64

structure CheckpointData where
  epoch : Nat
  root : List Nat
  deriving FromJson, ToJson

structure Data where
  slot : Nat
  bits : Nat
  previous : CheckpointData
  current : CheckpointData
  finalized : CheckpointData
  total : Nat
  previousBalance : Nat
  currentBalance : Nat
  rootSeed : Nat
  deriving FromJson, ToJson

structure Case where
  state : State
  balances : Balances
  rootSeed : Word

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def CheckpointData.decode (data : CheckpointData) : Except String Checkpoint := do
  require (data.epoch < 2^64 && data.root.all (· < 2^64)) "checkpoint integer outside uint64"
  let [a, b, c, d] := data.root | throw "checkpoint root must have four uint64 words"
  return ⟨BitVec.ofNat 64 data.epoch,
    ⟨BitVec.ofNat 64 a, BitVec.ofNat 64 b, BitVec.ofNat 64 c, BitVec.ofNat 64 d⟩⟩

private def timeValid (slot epoch : Nat) : Bool :=
  let start := epoch * 32
  start < slot && slot ≤ start + 8192 && start + 8192 < 2^64

def Data.decode (data : Data) : Except String Case := do
  require ([data.slot, data.total, data.previousBalance, data.currentBalance, data.rootSeed].all
    (· < 2^64)) "input integer outside uint64"
  require (data.bits < 16) "noncanonical justification bits"
  require (3 * data.previousBalance < 2^64 && 3 * data.currentBalance < 2^64 &&
    2 * data.total < 2^64) "balance multiplication outside uint64"
  require (data.previous.epoch + 3 < 2^64 && data.current.epoch + 2 < 2^64)
    "checkpoint addition outside uint64"
  let e := data.slot / 32
  require (!(3 * data.previousBalance ≥ 2 * data.total) || timeValid data.slot (e - 1))
    "previous root outside temporal precondition"
  require (!(3 * data.currentBalance ≥ 2 * data.total) || timeValid data.slot e)
    "current root outside temporal precondition"
  let state := State.mk (BitVec.ofNat 64 data.slot) (BitVec.ofNat 64 data.bits)
    (← data.previous.decode) (← data.current.decode) (← data.finalized.decode)
  return ⟨state, ⟨BitVec.ofNat 64 data.total, BitVec.ofNat 64 data.previousBalance,
    BitVec.ofNat 64 data.currentBalance⟩, BitVec.ofNat 64 data.rootSeed⟩

/-- Fixture data only: each index has distinct, non-palindromic little-endian words. -/
def rootAt (seed : Word) (index : Nat) : Root :=
  let i := BitVec.ofNat 64 index
  ⟨seed, i, seed ^^^ i, 0x1020304050607080 + i⟩

def encodeCheckpoint (checkpoint : Checkpoint) : CheckpointData :=
  ⟨checkpoint.epoch.toNat, [checkpoint.root.w0.toNat, checkpoint.root.w1.toNat,
    checkpoint.root.w2.toNat, checkpoint.root.w3.toNat]⟩

structure Result where
  slot : Nat
  bits : Nat
  previous : CheckpointData
  current : CheckpointData
  finalized : CheckpointData
  steps : Nat
  deriving ToJson

def result (state : State) (steps : Nat) : Result :=
  ⟨state.slot.toNat, state.bits.toNat, encodeCheckpoint state.previous,
    encodeCheckpoint state.current, encodeCheckpoint state.finalized, steps⟩

end ClAsm.Weigh.Input
