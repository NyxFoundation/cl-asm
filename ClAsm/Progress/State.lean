import ClAsm.Aggregate.State
import ClAsm.Progress.Program

namespace ClAsm.Progress

open ClAsm.Aggregate

end ClAsm.Progress

namespace ClAsm.Progress

open RiscvZkvm.Rv64 ClAsm.Aggregate

structure Addresses where
  entry : Word
  returnAddress : Word
  previousFlags : Word
  currentFlags : Word
  randaoMixes : Word
  slashings : Word
  eth1Count : Word
  deriving Repr, BEq, DecidableEq

structure Registers where
  t5 : Word := 0
  t6 : Word := 0
  t7 : Word := 0
  p11 : Word := 0
  p12 : Word := 0
  p13 : Word := 0
  x16 : Word := 0
  x17 : Word := 0
  x18 : Word := 0
  x19 : Word := 0
  x20 : Word := 0
  deriving Repr, BEq, DecidableEq

def Registers.owns (r : Registers) : Assertion :=
  (.x5 ↦ᵣ r.t5) ** (.x6 ↦ᵣ r.t6) ** (.x7 ↦ᵣ r.t7) ** (.x11 ↦ᵣ r.p11) **
    (.x12 ↦ᵣ r.p12) ** (.x13 ↦ᵣ r.p13) ** (.x16 ↦ᵣ r.x16) ** (.x17 ↦ᵣ r.x17) **
    (.x18 ↦ᵣ r.x18) ** (.x19 ↦ᵣ r.x19) ** (.x20 ↦ᵣ r.x20)

/-- One participation record per validator; count, previous and current
    flag arrays have the same length. -/
structure Input where
  slot : Word
  previousFlags : List Word
  currentFlags : List Word
  deriving Repr, BEq, DecidableEq

def epochOf (slot : Word) : Word := EpochAtSlot.epoch slot
def nextEpochOf (slot : Word) : Word := epochOf slot + signExtend12 1

/-- process_eth1_data_reset condition: the next epoch starts an eth1 voting
    period iff (epoch + 1) mod 64 = 0. -/
def eth1Condition (slot : Word) : Word := nextEpochOf slot &&& 63

def eth1ResetValue (slot old : Word) : Word :=
  if eth1Condition slot = 0 then 0 else old

/-- process_slashings_reset target: slashings[next_epoch % 8192]. -/
def slashPtr (slot : Word) (a : Addresses) : Word :=
  a.slashings + (((nextEpochOf slot) &&& 8191) <<< (3 : Nat))

/-- process_randao_mixes_reset source and target cells. -/
def randaoCurrPtr (slot : Word) (a : Addresses) : Word :=
  a.randaoMixes + (((epochOf slot) &&& 65535) <<< (3 : Nat))

def randaoNextPtr (slot : Word) (a : Addresses) : Word :=
  a.randaoMixes + (((nextEpochOf slot) &&& 65535) <<< (3 : Nat))

/-- The word produced by a plain LUI: (imm << 12), 32-bit wrap then sign extension. -/
def luiWord (imm : BitVec 20) : Word :=
  ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64

def callRegisters (count slot : Word) : Assertion :=
  (.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ count) ** (.x14 ↦ᵣ slot)

def arraysOwn (a : Addresses) (input : Input) : Assertion :=
  wordsOwn a.previousFlags input.previousFlags ** wordsOwn a.currentFlags input.currentFlags

theorem arraysOwn_pcFree (a : Addresses) (input : Input) : (arraysOwn a input).pcFree :=
  pcFree_sepConj (wordsOwn_pcFree _ _) (wordsOwn_pcFree _ _)

def zeroList (n : Nat) : List Word := List.replicate n 0

def disjointRanges (a sizeA b sizeB : Nat) : Prop := a + sizeA ≤ b ∨ b + sizeB ≤ a

structure ValidAddresses (a : Addresses) (n : Nat) : Prop where
  previousAligned : a.previousFlags.toNat % 8 = 0
  currentAligned : a.currentFlags.toNat % 8 = 0
  randaoAligned : a.randaoMixes.toNat % 8 = 0
  slashingsAligned : a.slashings.toNat % 8 = 0
  eth1Aligned : a.eth1Count.toNat % 8 = 0
  entryAligned : a.entry.toNat % 4 = 0
  returnAligned : a.returnAddress.toNat % 4 = 0
  concretePrevious : a.previousFlags = 0x70000000
  concreteCurrent : a.currentFlags = 0x71000000
  concreteRandao : a.randaoMixes = 0x72000000
  concreteSlashings : a.slashings = 0x73000000
  concreteEth1 : a.eth1Count = 0x74000000
  previousNoWrap : a.previousFlags.toNat + 8 * n < 2^64
  currentNoWrap : a.currentFlags.toNat + 8 * n < 2^64
  randaoNoWrap : a.randaoMixes.toNat + randaoSpan < 2^64
  slashingsNoWrap : a.slashings.toNat + slashingSpan < 2^64
  codeNoWrap : a.entry.toNat + 4 * program.length < 2^64
  previousCurrent : disjointRanges a.previousFlags.toNat (8 * n) a.currentFlags.toNat (8 * n)
  previousRandao : disjointRanges a.previousFlags.toNat (8 * n) a.randaoMixes.toNat randaoSpan
  previousSlashings : disjointRanges a.previousFlags.toNat (8 * n) a.slashings.toNat slashingSpan
  previousEth1 : disjointRanges a.previousFlags.toNat (8 * n) a.eth1Count.toNat 8
  currentRandao : disjointRanges a.currentFlags.toNat (8 * n) a.randaoMixes.toNat randaoSpan
  currentSlashings : disjointRanges a.currentFlags.toNat (8 * n) a.slashings.toNat slashingSpan
  currentEth1 : disjointRanges a.currentFlags.toNat (8 * n) a.eth1Count.toNat 8
  codePrevious : disjointRanges a.entry.toNat (4 * program.length) a.previousFlags.toNat (8 * n)
  codeCurrent : disjointRanges a.entry.toNat (4 * program.length) a.currentFlags.toNat (8 * n)
  codeRandao : disjointRanges a.entry.toNat (4 * program.length) a.randaoMixes.toNat randaoSpan
  codeSlashings : disjointRanges a.entry.toNat (4 * program.length) a.slashings.toNat slashingSpan
  codeEth1 : disjointRanges a.entry.toNat (4 * program.length) a.eth1Count.toNat 8
  returnOutside : a.returnAddress.toNat < a.entry.toNat ∨
    a.entry.toNat + 4 * program.length ≤ a.returnAddress.toNat

/-- The record update admits a validator count bounded by the fixed regions;
    the two randao cells of the update must differ (one self-overwriting epoch
    per randao period is outside the contract), and the slashings target cell
    must differ from the slashings base. -/
structure ValidInput (a : Addresses) (input : Input) : Prop where
  lengthEq : input.previousFlags.length = input.currentFlags.length
  countBound : input.currentFlags.length < flagCapacity
  randaoDistinct : randaoCurrPtr input.slot a ≠ randaoNextPtr input.slot a
  slashDistinct : ((nextEpochOf input.slot) &&& 8191) ≠ 0

def precondition (a : Addresses) (input : Input) (r : Registers)
    (oldEth1 oldSlash oldMix mixNext : Word) : Assertion :=
  r.owns ** callRegisters (BitVec.ofNat 64 input.currentFlags.length) input.slot **
    arraysOwn a input **
    ((a.eth1Count ↦ₘ oldEth1) ** (slashPtr input.slot a ↦ₘ oldSlash) **
      (randaoCurrPtr input.slot a ↦ₘ oldMix) ** (randaoNextPtr input.slot a ↦ₘ mixNext))

/-- Return preserves the inputs and stores all floored balances. -/
def postcondition (a : Addresses) (input : Input) (oldEth1 oldSlash oldMix : Word) : Assertion :=
  fun h => ∃ registers : Registers,
    (registers.owns ** callRegisters (BitVec.ofNat 64 input.currentFlags.length) input.slot **
      wordsOwn a.previousFlags input.currentFlags ** wordsOwn a.currentFlags
        (zeroList input.currentFlags.length) **
      (a.eth1Count ↦ₘ eth1ResetValue input.slot oldEth1) **
      (a.slashings ↦ₘ oldSlash) ** (slashPtr input.slot a ↦ₘ 0) **
      (randaoCurrPtr input.slot a ↦ₘ oldMix) ** (randaoNextPtr input.slot a ↦ₘ oldMix)) h

end ClAsm.Progress
