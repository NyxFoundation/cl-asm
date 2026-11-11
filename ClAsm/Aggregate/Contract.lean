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
  slot : Word
  scratchBase : Word
  returnAddress : Word
  deriving Repr, BEq, DecidableEq

def Registers.owns (a : Addresses) (r : Registers) : Assertion :=
  (.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ a.returnAddress) ** (.x14 ↦ᵣ r.slot) ** (.x15 ↦ᵣ a.scratch)

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

/-- The concrete witness-style calling registers. -/
def witnessRegisters (a : Addresses) (input : Input) : Registers :=
  ⟨input.slot, a.scratch, a.returnAddress⟩

/-- The routine's exact calling assertion. -/
def precondition (a : Addresses) (input : Input) (scratchT scratchP scratchC : Word) :
    Assertion :=
  fun h => ∃ registers : Registers,
    (Registers.owns a registers ** (.x10 ↦ᵣ a.validators) ** (.x11 ↦ᵣ a.previousFlags) **
      (.x12 ↦ᵣ a.currentFlags) ** (.x13 ↦ᵣ BitVec.ofNat 64 input.validators.length) ** 
      validatorsOwn a.validators input.validators ** wordsOwn a.previousFlags input.previousFlags **
      wordsOwn a.currentFlags input.currentFlags **
      (a.scratch ↦ₘ scratchT) ** (a.scratch + 8 ↦ₘ scratchP) ** (a.scratch + 16 ↦ₘ scratchC)) h

/-- On return the scratch holds the three saturated balances and every array
    is preserved. -/
def postcondition (a : Addresses) (input : Input) : Assertion :=
  fun h => ∃ registers : Registers,
    (Registers.owns a registers ** (a.scratch ↦ₘ (aggregateResult input).1) **
      (a.scratch + 8 ↦ₘ (aggregateResult input).2.1) **
      (a.scratch + 16 ↦ₘ (aggregateResult input).2.2) **
      validatorsOwn a.validators input.validators ** wordsOwn a.previousFlags input.previousFlags **
      wordsOwn a.currentFlags input.currentFlags) h

end ClAsm.Aggregate
