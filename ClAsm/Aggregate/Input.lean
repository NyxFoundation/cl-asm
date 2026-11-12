import ClAsm.Aggregate.Contract
import Lean.Data.Json

namespace ClAsm.Aggregate.Input

open Lean RiscvZkvm.Rv64

structure ValidatorData where
  effectiveBalance : Nat
  activationEpoch : Nat
  exitEpoch : Nat
  slashed : Nat
  deriving FromJson, ToJson

structure Data where
  slot : Nat
  validators : List ValidatorData
  previousFlags : List Nat
  currentFlags : List Nat
  deriving FromJson, ToJson

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def ValidatorData.decode (data : ValidatorData) : Except String Validator := do
  require ([data.effectiveBalance, data.activationEpoch, data.exitEpoch].all (· < 2^64))
    "validator integer outside uint64"
  require (data.slashed ≤ 1) "noncanonical slashed flag"
  return ⟨BitVec.ofNat 64 data.effectiveBalance, BitVec.ofNat 64 data.activationEpoch,
    BitVec.ofNat 64 data.exitEpoch, BitVec.ofNat 64 data.slashed⟩

def Data.decode (data : Data) : Except String Aggregate.Input := do
  require (data.slot < 2^64) "slot outside uint64"
  require (data.validators.length ≤ capacity) "validator count exceeds layout capacity"
  require (data.previousFlags.length == data.validators.length &&
    data.currentFlags.length == data.validators.length) "participation length mismatch"
  require ((data.previousFlags ++ data.currentFlags).all (· < 256))
    "participation flag outside uint8"
  let input : Aggregate.Input := ⟨BitVec.ofNat 64 data.slot, ← data.validators.mapM (·.decode),
    data.previousFlags.map (BitVec.ofNat 64), data.currentFlags.map (BitVec.ofNat 64)⟩
  require (sumActive input.validators (currentEpoch input) < 2^64 &&
    sumTarget input.validators input.previousFlags (previousEpochWord input) < 2^64 &&
    sumTarget input.validators input.currentFlags (currentEpoch input) < 2^64)
    "balance sum outside uint64"
  return input

structure Result where
  total : Nat
  previous : Nat
  current : Nat
  steps : Nat
  deriving ToJson

def result (values : Word × Word × Word) (steps : Nat) : Result :=
  ⟨values.1.toNat, values.2.1.toNat, values.2.2.toNat, steps⟩

end ClAsm.Aggregate.Input
