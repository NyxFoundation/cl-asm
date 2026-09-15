import ClAsm.Weigh.Program
import ClAsm.Weigh.State
import ClAsm.EpochAtSlot.Proof
import ClAsm.Arithmetic.Proof
import ClAsm.Checkpoint.Proof

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

structure PrologueRegisters where
  temporary : Word
  source : Word
  target : Word
  epoch : Word
  previousEpoch : Word
  bits : Word

def PrologueRegisters.owns (ptr scratch : Word) (r : PrologueRegisters) : Assertion :=
  (.x10 ↦ᵣ ptr) ** (.x15 ↦ᵣ scratch) ** (.x5 ↦ᵣ r.temporary) ** (.x6 ↦ᵣ r.source) **
    (.x7 ↦ᵣ r.target) ** (.x16 ↦ᵣ r.epoch) ** (.x17 ↦ᵣ r.previousEpoch) ** (.x28 ↦ᵣ r.bits)

def prologueRegisters (ptr : Word) (state : State) : PrologueRegisters :=
  ⟨state.current.root.w3, ptr + 56, ptr + 16, EpochAtSlot.epoch state.slot,
    Arithmetic.previousValue (EpochAtSlot.epoch state.slot), Arithmetic.shiftedBits state.bits⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem prologue_spec (base ptr scratch : Word) (state : State) (r : PrologueRegisters)
    (oldScratch0 oldScratch1 : Checkpoint) :
    cpsTripleWithin prologue.length base (base + 172) (CodeReq.ofProg base prologue)
      (r.owns ptr scratch ** state.owns ptr ** oldScratch0.owns scratch ** oldScratch1.owns (scratch + 40))
      ((prologueRegisters ptr state).owns ptr scratch **
        State.owns ptr { state with previous := state.current } **
        state.previous.owns scratch ** state.current.owns (scratch + 40)) := by
  unfold prologue prologueRegisters PrologueRegisters.owns State.owns Checkpoint.owns
  simp only [copyCheckpoint, EpochAtSlot.program, Arithmetic.previousEpoch,
    Arithmetic.shiftJustificationBits, List.cons_append, List.nil_append,
    CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have a0 := addi_spec_gen_within .x6 .x10 r.source ptr 16 base (by decide)
  have a1 := addi_spec_gen_within .x7 .x15 r.target scratch 0 (base + 4) (by decide)
  have c0 := copyCheckpoint_spec .x6 .x7 .x5 (base + 8) (ptr + 16) scratch
    r.temporary state.previous oldScratch0 (by decide) (by decide)
  have a2 := addi_spec_gen_within .x6 .x10 (ptr + 16) ptr 56 (base + 48) (by decide)
  have a3 := addi_spec_gen_within .x7 .x15 scratch scratch 40 (base + 52) (by decide)
  have c1 := copyCheckpoint_spec .x6 .x7 .x5 (base + 56) (ptr + 56) (scratch + 40)
    state.previous.root.w3 state.current oldScratch1 (by decide) (by decide)
  have a4 := addi_spec_gen_within .x7 .x10 (scratch + 40) ptr 16 (base + 96) (by decide)
  have c2 := copyCheckpoint_spec .x6 .x7 .x5 (base + 100) (ptr + 56) (ptr + 16)
    state.current.root.w3 state.current state.previous (by decide) (by decide)
  have e := EpochAtSlot.program_spec .x10 .x16 (base + 140) ptr state.slot r.epoch (by decide) (by decide)
  have p := Arithmetic.previousEpoch_spec .x16 .x17 (base + 148)
    (EpochAtSlot.epoch state.slot) r.previousEpoch (by decide) (by decide)
  have b := ld_spec_within .x28 .x10 ptr r.bits state.bits 8 (base + 160) (by decide)
  have shift := Arithmetic.shiftJustificationBits_spec .x28 (base + 164) state.bits (by decide)
  simp only [copyCheckpoint, Checkpoint.owns, EpochAtSlot.program, Arithmetic.previousEpoch,
    Arithmetic.shiftJustificationBits, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    List.length_cons, List.length_nil] at c0 c1 c2 e p shift
  runBlock a0 a1 c0 a2 a3 c1 a4 c2 e p b shift

end ClAsm.Weigh
