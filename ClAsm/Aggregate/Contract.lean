import ClAsm.Aggregate.Program
import ClAsm.Aggregate.State

namespace ClAsm.Aggregate

open RiscvZkvm.Rv64

structure Addresses where
  entry : Word
  returnAddress : Word
  validators : Word
  previousFlags : Word
  currentFlags : Word
  scratch : Word
  deriving Repr, BEq, DecidableEq

structure Registers where
  t5 : Word := 0
  t6 : Word := 0
  t7 : Word := 0
  epoch : Word := 0
  total : Word := 0
  increment : Word := 0
  previous : Word := 0
  current : Word := 0
  previousEpoch : Word := 0
  deriving Repr, BEq, DecidableEq

def Registers.owns (r : Registers) : Assertion :=
  (.x5 ↦ᵣ r.t5) ** (.x6 ↦ᵣ r.t6) ** (.x7 ↦ᵣ r.t7) ** (.x16 ↦ᵣ r.epoch) **
    (.x17 ↦ᵣ r.total) ** (.x28 ↦ᵣ r.increment) ** (.x29 ↦ᵣ r.previous) **
    (.x30 ↦ᵣ r.current) ** (.x31 ↦ᵣ r.previousEpoch)

def callRegisters (a : Addresses) (input : Input) (processed : Nat) : Assertion :=
  (.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ a.returnAddress) ** (.x14 ↦ᵣ input.slot) ** (.x15 ↦ᵣ a.scratch) **
    (.x10 ↦ᵣ a.validators + BitVec.ofNat 64 (32 * processed)) **
    (.x11 ↦ᵣ a.previousFlags + BitVec.ofNat 64 (8 * processed)) **
    (.x12 ↦ᵣ a.currentFlags + BitVec.ofNat 64 (8 * processed)) **
    (.x13 ↦ᵣ BitVec.ofNat 64 (input.validators.length - processed))

def arraysOwn (a : Addresses) (input : Input) : Assertion :=
  validatorsOwn a.validators input.validators ** wordsOwn a.previousFlags input.previousFlags **
    wordsOwn a.currentFlags input.currentFlags

theorem arraysOwn_pcFree (a : Addresses) (input : Input) : (arraysOwn a input).pcFree :=
  pcFree_sepConj (validatorsOwn_pcFree _ _)
    (pcFree_sepConj (wordsOwn_pcFree _ _) (wordsOwn_pcFree _ _))

def scratchOwn (a : Addresses) (total previous current : Word) : Assertion :=
  ((a.scratch + signExtend12 0) ↦ₘ total) **
    ((a.scratch + signExtend12 8) ↦ₘ previous) **
    ((a.scratch + signExtend12 16) ↦ₘ current)

def disjointRanges (a sizeA b sizeB : Nat) : Prop := a + sizeA ≤ b ∨ b + sizeB ≤ a

structure ValidAddresses (a : Addresses) (n : Nat) : Prop where
  validatorsAligned : a.validators.toNat % 8 = 0
  previousFlagsAligned : a.previousFlags.toNat % 8 = 0
  currentFlagsAligned : a.currentFlags.toNat % 8 = 0
  scratchAligned : a.scratch.toNat % 8 = 0
  entryAligned : a.entry.toNat % 4 = 0
  returnAligned : a.returnAddress.toNat % 4 = 0
  validatorsNoWrap : a.validators.toNat + 32 * n < 2^64
  previousFlagsNoWrap : a.previousFlags.toNat + 8 * n < 2^64
  currentFlagsNoWrap : a.currentFlags.toNat + 8 * n < 2^64
  scratchNoWrap : a.scratch.toNat + answerBytes < 2^64
  codeNoWrap : a.entry.toNat + 4 * program.length < 2^64
  validatorsFlags : disjointRanges a.validators.toNat (32 * n) a.previousFlags.toNat (8 * n)
  validatorsCurrent : disjointRanges a.validators.toNat (32 * n) a.currentFlags.toNat (8 * n)
  validatorsScratch : disjointRanges a.validators.toNat (32 * n) a.scratch.toNat answerBytes
  previousCurrent : disjointRanges a.previousFlags.toNat (8 * n) a.currentFlags.toNat (8 * n)
  previousScratch : disjointRanges a.previousFlags.toNat (8 * n) a.scratch.toNat answerBytes
  currentScratch : disjointRanges a.currentFlags.toNat (8 * n) a.scratch.toNat answerBytes
  codeValidators : disjointRanges a.entry.toNat (4 * program.length) a.validators.toNat (32 * n)
  codePrevious : disjointRanges a.entry.toNat (4 * program.length) a.previousFlags.toNat (8 * n)
  codeCurrent : disjointRanges a.entry.toNat (4 * program.length) a.currentFlags.toNat (8 * n)
  codeScratch : disjointRanges a.entry.toNat (4 * program.length) a.scratch.toNat answerBytes
  returnOutside : a.returnAddress.toNat < a.entry.toNat ∨
    a.entry.toNat + 4 * program.length ≤ a.returnAddress.toNat

/-- The three balances stay inside uint64 before the increment floor is applied. -/
structure ValidInput (input : Input) : Prop where
  previousLength : input.previousFlags.length = input.validators.length
  currentLength : input.currentFlags.length = input.validators.length
  flags : ∀ f ∈ input.previousFlags ++ input.currentFlags, f.toNat < 256
  slashed : ∀ v ∈ input.validators, v.slashed = 0 ∨ v.slashed = 1
  active : sumActive input.validators (currentEpoch input) < 2^64
  previous : sumTarget input.validators input.previousFlags
    (previousEpochWord input) < 2^64
  current : sumTarget input.validators input.currentFlags
    (currentEpoch input) < 2^64

def precondition (a : Addresses) (input : Input) (registers : Registers)
    (scratchT scratchP scratchC : Word) : Assertion :=
  registers.owns ** callRegisters a input 0 ** arraysOwn a input **
    scratchOwn a scratchT scratchP scratchC

/-- Return preserves the inputs and stores all three increment-floored balances. -/
def postcondition (a : Addresses) (input : Input) : Assertion :=
  fun h => ∃ registers : Registers,
    (registers.owns ** callRegisters a input input.validators.length ** arraysOwn a input **
      scratchOwn a (aggregateResult input).1 (aggregateResult input).2.1
        (aggregateResult input).2.2) h

end ClAsm.Aggregate
