import ClAsm.Weigh.Program
import ClAsm.Arithmetic.Proof
import ClAsm.Weigh.Branch
import ClAsm.Checkpoint.Proof
import ClAsm.Weigh.Contract

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

def zeroBit (value : Word) : Word := if BitVec.ult value (signExtend12 1) then 1 else 0

def epochMatch (oldEpoch currentEpoch : Word) (delta : BitVec 12) : Word :=
  zeroBit ((oldEpoch + signExtend12 delta) ^^^ currentEpoch)

def finalizationValue (bits oldEpoch currentEpoch : Word) (delta mask : BitVec 12) : Word :=
  zeroBit ((bits &&& signExtend12 mask) ^^^ signExtend12 mask) &&& epochMatch oldEpoch currentEpoch delta

theorem zeroBit_eq (value : Word) : zeroBit value = if value = 0 then 1 else 0 := by
  have h : value.toNat < 1 ↔ value = 0 := by
    constructor
    · intro hn
      apply BitVec.eq_of_toNat_eq
      change value.toNat = 0
      omega
    · intro hv
      subst hv
      decide
  by_cases hv : value = 0
  · subst hv
    decide
  · have hn : ¬ value.toNat < 1 := fun hn => hv (h.mp hn)
    simp [zeroBit, BitVec.ult, signExtend12, hn]
    exact hv

theorem finalizationValue_eq (bits oldEpoch currentEpoch : Word) (delta mask : BitVec 12) :
    finalizationValue bits oldEpoch currentEpoch delta mask =
      if bits &&& signExtend12 mask = signExtend12 mask ∧
        oldEpoch + signExtend12 delta = currentEpoch then 1 else 0 := by
  by_cases hm : bits &&& signExtend12 mask = signExtend12 mask <;>
    by_cases he : oldEpoch + signExtend12 delta = currentEpoch <;>
    simp [finalizationValue, epochMatch, zeroBit_eq, BitVec.xor_eq_zero_iff, hm, he]

theorem finalizationValue_correct (bits oldEpoch currentEpoch : Word) (delta mask : BitVec 12)
    (hd : (signExtend12 delta).toNat = delta.toNat)
    (hm : (signExtend12 mask).toNat = mask.toNat)
    (hadd : oldEpoch.toNat + delta.toNat < 2^64) :
    finalizationValue bits oldEpoch currentEpoch delta mask =
      if bits.toNat &&& mask.toNat = mask.toNat ∧
        oldEpoch.toNat + delta.toNat = currentEpoch.toNat then 1 else 0 := by
  rw [finalizationValue_eq]
  have hmask : bits &&& signExtend12 mask = signExtend12 mask ↔
      bits.toNat &&& mask.toNat = mask.toNat := by
    rw [BitVec.toNat_eq, BitVec.toNat_and, hm]
  have hepoch : oldEpoch + signExtend12 delta = currentEpoch ↔
      oldEpoch.toNat + delta.toNat = currentEpoch.toNat := by
    rw [BitVec.toNat_eq, BitVec.toNat_add, hd, Nat.mod_eq_of_lt hadd]
  simp only [hmask, hepoch]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem finalizationCondition_spec (base scratch bits oldEpoch currentEpoch oldPredicate oldComparison : Word)
    (offset delta mask : BitVec 12) :
    cpsTripleWithin (finalizationCondition offset delta mask).length base (base + 32)
      (CodeReq.ofProg base (finalizationCondition offset delta mask))
      ((.x15 ↦ᵣ scratch) ** (.x28 ↦ᵣ bits) ** (.x16 ↦ᵣ currentEpoch) **
        (.x29 ↦ᵣ oldPredicate) ** (.x31 ↦ᵣ oldComparison) **
        (scratch + signExtend12 offset ↦ₘ oldEpoch))
      ((.x15 ↦ᵣ scratch) ** (.x28 ↦ᵣ bits) ** (.x16 ↦ᵣ currentEpoch) **
        (.x29 ↦ᵣ finalizationValue bits oldEpoch currentEpoch delta mask) **
        (.x31 ↦ᵣ epochMatch oldEpoch currentEpoch delta) **
        (scratch + signExtend12 offset ↦ₘ oldEpoch)) := by
  unfold finalizationCondition
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have a := andi_spec_gen_within .x29 .x28 oldPredicate bits mask base (by decide)
  have b := xori_spec_gen_same_within .x29 (bits &&& signExtend12 mask) mask (base + 4) (by decide)
  have c : cpsTripleWithin 1 (base + 8) (base + 8 + 4)
      (CodeReq.singleton (base + 8) (.SLTIU .x29 .x29 1))
      (.x29 ↦ᵣ (bits &&& signExtend12 mask) ^^^ signExtend12 mask)
      (.x29 ↦ᵣ zeroBit ((bits &&& signExtend12 mask) ^^^ signExtend12 mask)) := by
    exact sltiu_spec_gen_same_within .x29
      ((bits &&& signExtend12 mask) ^^^ signExtend12 mask) 1 (base + 8) (by decide)
  have d := ld_spec_within .x31 .x15 scratch oldComparison oldEpoch offset (base + 12) (by decide)
  have e := addi_spec_gen_same_within .x31 oldEpoch delta (base + 16) (by decide)
  have f := xor_spec_gen_rd_eq_rs1_within .x31 .x16 (oldEpoch + signExtend12 delta)
    currentEpoch (base + 20) (by decide)
  have g : cpsTripleWithin 1 (base + 24) (base + 24 + 4)
      (CodeReq.singleton (base + 24) (.SLTIU .x31 .x31 1))
      (.x31 ↦ᵣ (oldEpoch + signExtend12 delta) ^^^ currentEpoch)
      (.x31 ↦ᵣ epochMatch oldEpoch currentEpoch delta) := by
    exact sltiu_spec_gen_same_within .x31
      ((oldEpoch + signExtend12 delta) ^^^ currentEpoch) 1 (base + 24) (by decide)
  have h := and_spec_gen_rd_eq_rs1_within .x29 .x31
    (zeroBit ((bits &&& signExtend12 mask) ^^^ signExtend12 mask))
    (epochMatch oldEpoch currentEpoch delta) (base + 28) (by decide)
  unfold finalizationValue
  runBlock a b c d e f g h

theorem finalizeBody_spec (base ptr scratch oldSource oldTarget oldTmp : Word)
    (offset : BitVec 12) (saved oldFinalized : Checkpoint) :
    cpsTripleWithin (finalizeBody offset).length base (base + 48)
      (CodeReq.ofProg base (finalizeBody offset))
      ((.x10 ↦ᵣ ptr) ** (.x15 ↦ᵣ scratch) ** (.x6 ↦ᵣ oldSource) **
        (.x7 ↦ᵣ oldTarget) ** (.x5 ↦ᵣ oldTmp) **
        saved.owns (scratch + signExtend12 offset) ** oldFinalized.owns (ptr + 96))
      ((.x10 ↦ᵣ ptr) ** (.x15 ↦ᵣ scratch) ** (.x6 ↦ᵣ scratch + signExtend12 offset) **
        (.x7 ↦ᵣ ptr + 96) ** (.x5 ↦ᵣ saved.root.w3) **
        saved.owns (scratch + signExtend12 offset) ** saved.owns (ptr + 96)) := by
  have a := addi_spec_gen_within .x6 .x15 oldSource scratch offset base (by decide)
  have b := addi_spec_gen_within .x7 .x10 oldTarget ptr 96 (base + 4) (by decide)
  have c := copyCheckpoint_spec .x6 .x7 .x5 (base + 8) (scratch + signExtend12 offset)
    (ptr + 96) oldTmp saved oldFinalized (by decide) (by decide)
  simp only [finalizeBody, copyCheckpoint, Checkpoint.owns, List.cons_append, List.nil_append,
    CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil] at c ⊢
  runBlock a b c

def finalizeRegisters (a : Addresses) (r : Registers) (saved : Checkpoint)
    (offset delta mask : BitVec 12) : Registers :=
  let value := finalizationValue r.prologue.bits saved.epoch r.prologue.epoch delta mask
  { r with
    predicate := value
    comparison := epochMatch saved.epoch r.prologue.epoch delta
    prologue := if value = 0 then r.prologue else
      { r.prologue with
        source := a.scratch + signExtend12 offset
        target := a.state + 96
        temporary := saved.root.w3 } }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem finalize_spec (base : Word) (a : Addresses) (balances : Balances) (r : Registers)
    (saved oldFinalized : Checkpoint) (offset delta mask : BitVec 12) :
    cpsTripleWithin (finalize offset delta mask).length base (base + 88)
      (CodeReq.ofProg base (finalize offset delta mask))
      (r.owns a balances ** saved.owns (a.scratch + signExtend12 offset) **
        oldFinalized.owns (a.state + 96))
      ((finalizeRegisters a r saved offset delta mask).owns a balances **
        saved.owns (a.scratch + signExtend12 offset) **
        (if finalizationValue r.prologue.bits saved.epoch r.prologue.epoch delta mask = 0
          then oldFinalized else saved).owns (a.state + 96)) := by
  have condition := finalizationCondition_spec base a.scratch r.prologue.bits saved.epoch
    r.prologue.epoch r.predicate r.comparison offset delta mask
  have branch := branchNonzero_spec (base + 32)
    (finalizationValue r.prologue.bits saved.epoch r.prologue.epoch delta mask)
  have skip := jal_x0_spec_gen_within 52 (base + 36)
  simp only [show signExtend21 (52 : BitVec 21) = (52 : Word) from by decide] at skip
  have body := finalizeBody_spec (base + 40) a.state a.scratch
    r.prologue.source r.prologue.target r.prologue.temporary offset saved oldFinalized
  unfold finalizeRegisters Registers.owns PrologueRegisters.owns
  simp only [finalize, finalizationCondition, finalizeBody, if_eq, copyCheckpoint,
    Checkpoint.owns, List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    CodeReq.ofProg_cons, CodeReq.ofProg_nil] at condition body ⊢
  by_cases h : finalizationValue r.prologue.bits saved.epoch r.prologue.epoch delta mask = 0
  · simp only [h, if_true] at condition branch ⊢
    runBlock condition branch skip
  · simp only [h, if_false] at branch ⊢
    runBlock condition branch body

end ClAsm.Weigh
