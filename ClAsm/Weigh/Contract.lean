import ClAsm.Weigh.Prologue

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

structure Registers where
  prologue : PrologueRegisters
  predicate : Word
  twiceTotal : Word
  comparison : Word

structure Addresses where
  entry : Word
  state : Word
  roots : Word
  scratch : Word
  returnAddress : Word

def Registers.owns (a : Addresses) (balances : Balances) (r : Registers) : Assertion :=
  (.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ a.returnAddress) ** (.x11 ↦ᵣ a.roots) **
    (.x12 ↦ᵣ balances.total) ** (.x13 ↦ᵣ balances.previous) ** (.x14 ↦ᵣ balances.current) **
    r.prologue.owns a.state a.scratch ** (.x29 ↦ᵣ r.predicate) **
    (.x30 ↦ᵣ r.twiceTotal) ** (.x31 ↦ᵣ r.comparison)

def disjointRanges (a sizeA b sizeB : Nat) : Prop := a + sizeA ≤ b ∨ b + sizeB ≤ a

structure ValidAddresses (a : Addresses) : Prop where
  stateAligned : a.state.toNat % 8 = 0
  rootsAligned : a.roots.toNat % 8 = 0
  scratchAligned : a.scratch.toNat % 8 = 0
  entryAligned : a.entry.toNat % 4 = 0
  returnAligned : a.returnAddress.toNat % 4 = 0
  stateNoWrap : a.state.toNat + Layout.stateBytes < 2^64
  rootsNoWrap : a.roots.toNat + Layout.rootsBytes < 2^64
  scratchNoWrap : a.scratch.toNat + Layout.scratchBytes < 2^64
  codeNoWrap : a.entry.toNat + 4 * program.length < 2^64
  stateRoots : disjointRanges a.state.toNat Layout.stateBytes a.roots.toNat Layout.rootsBytes
  stateScratch : disjointRanges a.state.toNat Layout.stateBytes a.scratch.toNat Layout.scratchBytes
  rootsScratch : disjointRanges a.roots.toNat Layout.rootsBytes a.scratch.toNat Layout.scratchBytes
  codeState : disjointRanges a.entry.toNat (4 * program.length) a.state.toNat Layout.stateBytes
  codeRoots : disjointRanges a.entry.toNat (4 * program.length) a.roots.toNat Layout.rootsBytes
  codeScratch : disjointRanges a.entry.toNat (4 * program.length) a.scratch.toNat Layout.scratchBytes
  returnOutside : a.returnAddress.toNat < a.entry.toNat ∨
    a.entry.toNat + 4 * program.length ≤ a.returnAddress.toNat

abbrev RootArray := Fin Layout.slotsPerHistoricalRoot → Root

def RootArray.at (roots : RootArray) (index : Nat) : Root :=
  roots ⟨index % Layout.slotsPerHistoricalRoot, Nat.mod_lt _ (by decide)⟩

def precondition (a : Addresses) (state : State) (balances : Balances) (r : Registers)
    (roots : RootArray) (scratch0 scratch1 : Checkpoint) : Assertion :=
  r.owns a balances ** state.owns a.state ** rootsOwn a.roots (List.ofFn roots) **
    scratch0.owns a.scratch ** scratch1.owns (a.scratch + 40)

/-- Scratch contains the saved old checkpoints; final temporary values are private. -/
def postcondition (a : Addresses) (state : State) (balances : Balances) (roots : RootArray) : Assertion :=
  fun h => ∃ registers : Registers,
    (registers.owns a balances ** (transition state balances roots.at).owns a.state **
      rootsOwn a.roots (List.ofFn roots) ** state.previous.owns a.scratch **
      state.current.owns (a.scratch + 40)) h

end ClAsm.Weigh
