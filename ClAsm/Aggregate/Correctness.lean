import ClAsm.Aggregate.Loop
import RiscvZkvm.Rv64.Logic.InstructionSpecs
import RiscvZkvm.Rv64.Logic.ControlFlow
import RiscvZkvm.Rv64.Logic.SyscallSpecs
import RiscvZkvm.Rv64.Logic.Tactics.RunBlock
import RiscvZkvm.Rv64.Logic.Tactics.XPerm

namespace ClAsm.Aggregate

open RiscvZkvm.Rv64

set_option maxHeartbeats 2000000 in
theorem prologue_spec (base slot t16 t17 t28 t29 t30 t31 : Word) :
    cpsTripleWithin prologue.length base (base + 36) (CodeReq.ofProg base prologue)
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ slot) ** (.x16 ↦ᵣ t16) ** (.x17 ↦ᵣ t17) **
        (.x28 ↦ᵣ t28) ** (.x29 ↦ᵣ t29) ** (.x30 ↦ᵣ t30) ** (.x31 ↦ᵣ t31))
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ slot) **
        (.x16 ↦ᵣ slot >>> (5 : BitVec 6).toNat) **
        (.x17 ↦ᵣ 0 + signExtend12 0) **
        (.x28 ↦ᵣ (((0x3B9AD : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 +
          signExtend12 0xA00) **
        (.x29 ↦ᵣ 0 + signExtend12 0) ** (.x30 ↦ᵣ 0 + signExtend12 0) **
        (.x31 ↦ᵣ Arithmetic.previousValue (slot >>> (5 : BitVec 6).toNat))) := by
  unfold prologue Arithmetic.previousEpoch Arithmetic.previousValue
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append]
  runBlock

theorem prologue_meaning (base slot t16 t17 t28 t29 t30 t31 : Word) :
    cpsTripleWithin prologue.length base (base + 36) (CodeReq.ofProg base prologue)
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ slot) ** (.x16 ↦ᵣ t16) ** (.x17 ↦ᵣ t17) **
        (.x28 ↦ᵣ t28) ** (.x29 ↦ᵣ t29) ** (.x30 ↦ᵣ t30) ** (.x31 ↦ᵣ t31))
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ slot) ** (.x16 ↦ᵣ EpochAtSlot.epoch slot) **
        (.x17 ↦ᵣ 0) ** (.x28 ↦ᵣ incrementWord) ** (.x29 ↦ᵣ 0) ** (.x30 ↦ᵣ 0) **
        (.x31 ↦ᵣ Arithmetic.previousValue (EpochAtSlot.epoch slot))) := by
  have spec := prologue_spec base slot t16 t17 t28 t29 t30 t31
  have hshift : (5 : BitVec 6).toNat = 5 := by decide
  have hzero : (0 : Word) + signExtend12 0 = 0 := by
    rw [zeroSign]
    exact BitVec.add_zero (x := 0)
  simp only [hshift, hzero] at spec
  exact spec

theorem signExtend13_eight : signExtend13 (8 : BitVec 13) = (8 : Word) := by
  simp only [signExtend13]
  bv_decide

theorem loopGuard_exit (head : Word) :
    cpsTripleWithin 2 head ((head + 4) + signExtend21 loopExitOffset)
      (CodeReq.ofProg head loopGuard)
      ((.x13 ↦ᵣ 0) ** (.x0 ↦ᵣ 0))
      ((.x13 ↦ᵣ 0) ** (.x0 ↦ᵣ 0)) := by
  unfold loopGuard
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  have branch := bne_spec_within .x13 .x0 8 0 0 head
  have fallen := cpsBranchWithin_ntakenStripPure2 branch (by
    intro _ h
    rcases h with ⟨_, _, _, _, _, hrest⟩
    rcases hrest with ⟨_, _, _, _, _, hpure⟩
    rcases hpure with ⟨_, hfalse⟩
    exact absurd rfl hfalse)
  have jump := cpsTripleWithin_frameR ((.x13 ↦ᵣ 0) ** (.x0 ↦ᵣ 0)) (by pcFree)
    (jal_x0_spec_gen_within loopExitOffset (head + 4))
  simp only [sepConj_emp_left'] at jump
  have hd : CodeReq.Disjoint (CodeReq.singleton head (.BNE .x13 .x0 8))
      (CodeReq.singleton (head + 4) (.JAL .x0 loopExitOffset)) := by
    intro addr
    by_cases h : addr = head
    · right
      subst h
      simp [CodeReq.singleton]
    · left
      simp [CodeReq.singleton, h]
  have exited := cpsTripleWithin_seq hd fallen jump
  simpa [CodeReq.union_empty_right] using exited

theorem loopGuard_taken (head counter : Word) (hneq : counter ≠ 0) :
    cpsTripleWithin 1 head (head + 8) (CodeReq.singleton head (.BNE .x13 .x0 8))
      ((.x13 ↦ᵣ counter) ** (.x0 ↦ᵣ 0))
      ((.x13 ↦ᵣ counter) ** (.x0 ↦ᵣ 0)) := by
  have branch := bne_spec_within .x13 .x0 8 counter 0 head
  have taken := cpsBranchWithin_takenStripPure2 branch (by
    intro _ h
    rcases h with ⟨_, _, _, _, _, hrest⟩
    rcases hrest with ⟨_, _, _, _, _, hpure⟩
    rcases hpure with ⟨_, heq⟩
    exact hneq heq)
  rw [signExtend13_eight] at taken
  exact taken

theorem backJump_spec (head : Word) :
    cpsTripleWithin 1 (head + 208) head (CodeReq.singleton (head + 208) (.JAL .x0 loopBackOffset))
      empAssertion empAssertion := by
  have jump := jal_x0_spec_gen_within loopBackOffset (head + 208)
  have htarget : (head + 208) + signExtend21 loopBackOffset = head := by
    have h := loopBackTarget (head + 208) head rfl
    simpa using h
  rw [htarget] at jump
  exact jump

theorem loop_has_guard (head : Word) :
    ∀ a i, (CodeReq.singleton head (.BNE .x13 .x0 8)) a = some i →
      (CodeReq.ofProg head loop) a = some i := by
  intro a i h
  have hsub := CodeReq.ofProg_mono_sub head head loop [.BNE .x13 .x0 8] 0
    (by rw [BitVec.add_zero]) (by decide) (by decide) (by decide) a i
  simpa [CodeReq.ofProg_singleton] using hsub h

theorem loop_has_body (head : Word) :
    ∀ a i, (CodeReq.ofProg (head + 8) bodyStraight) a = some i →
      (CodeReq.ofProg head loop) a = some i := by
  have hsub := CodeReq.ofProg_mono_sub head (head + 8) loop bodyStraight 2
    (by rfl) (by decide) (by decide) (by decide)
  exact hsub

theorem loop_has_back (head : Word) :
    ∀ a i, (CodeReq.singleton (head + 208) (.JAL .x0 loopBackOffset)) a = some i →
      (CodeReq.ofProg head loop) a = some i := by
  intro a i h
  have hsub := CodeReq.ofProg_mono_sub head (head + 208) loop [.JAL .x0 loopBackOffset] 52
    (by rfl) (by decide) (by decide) (by decide) a i
  simpa [CodeReq.ofProg_singleton] using hsub h

theorem oneIteration (head ptr prevPtr currPtr counter epoch previous total prevAcc currAcc
    t5 t6 t7 prevFlag currFlag : Word) (validator : Validator) (hneq : counter ≠ 0) :
    cpsTripleWithin 52 head head (CodeReq.ofProg head loop)
      ((((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ total) **
            (.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7) ** validator.owns ptr) **
          ((.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter) **
            (.x31 ↦ᵣ previous) ** (.x29 ↦ᵣ prevAcc) ** (.x30 ↦ᵣ currAcc) **
            ((prevPtr + signExtend12 0) ↦ₘ prevFlag) ** ((currPtr + signExtend12 0) ↦ₘ currFlag))))
      ((((.x10 ↦ᵣ ptr + signExtend12 32) ** (.x11 ↦ᵣ prevPtr + signExtend12 8) **
            (.x12 ↦ᵣ currPtr + signExtend12 8) ** (.x13 ↦ᵣ counter + signExtend12 4095)) **
          (((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) **
              (.x30 ↦ᵣ foldedTarget currAcc epoch validator currFlag) **
              (.x5 ↦ᵣ targetBit epoch validator currFlag) **
              (.x6 ↦ᵣ selectedTarget epoch validator currFlag) **
              (.x7 ↦ᵣ targetMask epoch validator currFlag) ** validator.owns ptr **
              ((currPtr + signExtend12 0) ↦ₘ currFlag)) **
            ((.x31 ↦ᵣ previous) **
              (.x29 ↦ᵣ foldedTarget prevAcc previous validator prevFlag) **
              ((prevPtr + signExtend12 0) ↦ₘ prevFlag) **
              (.x17 ↦ᵣ foldedActive total epoch validator))))) := by
  let rest : Assertion :=
    (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ total) ** (.x5 ↦ᵣ t5) **
      (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7) ** validator.owns ptr ** (.x11 ↦ᵣ prevPtr) **
      (.x12 ↦ᵣ currPtr) ** (.x31 ↦ᵣ previous) ** (.x29 ↦ᵣ prevAcc) **
      (.x30 ↦ᵣ currAcc) ** ((prevPtr + signExtend12 0) ↦ₘ prevFlag) **
      ((currPtr + signExtend12 0) ↦ₘ currFlag)
  have hrest : rest.pcFree := by unfold rest; pcFree
  have taken := cpsTripleWithin_extend_code (loop_has_guard head)
    (cpsTripleWithin_frameR rest hrest (loopGuard_taken head counter hneq))
  have hpre :
      (((.x13 ↦ᵣ counter) ** (.x0 ↦ᵣ 0)) ** rest) =
      ((((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ total) **
            (.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7) ** validator.owns ptr) **
          ((.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter) **
            (.x31 ↦ᵣ previous) ** (.x29 ↦ᵣ prevAcc) ** (.x30 ↦ᵣ currAcc) **
            ((prevPtr + signExtend12 0) ↦ₘ prevFlag) ** ((currPtr + signExtend12 0) ↦ₘ currFlag)))) := by
    unfold rest
    xperm
  rw [hpre] at taken
  have body := bodyStraight_spec (head + 8) ptr prevPtr currPtr counter epoch previous total
    prevAcc currAcc t5 t6 t7 prevFlag currFlag validator
  rw [bodyStraight_code] at body
  have body := cpsTripleWithin_extend_code (loop_has_body head) body
  have hend : (head + 8) + 184 + 16 = head + 208 := by bv_omega
  rw [hend] at body
  have stepped := cpsTripleWithin_seq_same_cr taken body
  have back := cpsTripleWithin_extend_code (loop_has_back head)
    (cpsTripleWithin_frameR _ (by
      have : ((((.x10 ↦ᵣ ptr + signExtend12 32) ** (.x11 ↦ᵣ prevPtr + signExtend12 8) **
            (.x12 ↦ᵣ currPtr + signExtend12 8) ** (.x13 ↦ᵣ counter + signExtend12 4095)) **
          (((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) **
              (.x30 ↦ᵣ foldedTarget currAcc epoch validator currFlag) **
              (.x5 ↦ᵣ targetBit epoch validator currFlag) **
              (.x6 ↦ᵣ selectedTarget epoch validator currFlag) **
              (.x7 ↦ᵣ targetMask epoch validator currFlag) ** validator.owns ptr **
              ((currPtr + signExtend12 0) ↦ₘ currFlag)) **
            ((.x31 ↦ᵣ previous) **
              (.x29 ↦ᵣ foldedTarget prevAcc previous validator prevFlag) **
              ((prevPtr + signExtend12 0) ↦ₘ prevFlag) **
              (.x17 ↦ᵣ foldedActive total epoch validator))))).pcFree := by pcFree
      exact this) (backJump_spec head))
  simp only [sepConj_emp_left'] at back
  exact cpsTripleWithin_seq_same_cr stepped back

theorem loop_has_guard_block (head : Word) :
    ∀ a i, (CodeReq.ofProg head loopGuard) a = some i →
      (CodeReq.ofProg head loop) a = some i := by
  exact CodeReq.ofProg_mono_sub head head loop loopGuard 0 (by rw [BitVec.add_zero])
    (by decide) (by decide) (by decide)

theorem counter_succ_ne (c : Nat) (hc : c + 1 < 2^64) :
    (BitVec.ofNat 64 (c + 1) : Word) ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc] at this
  simp [BitVec.toNat_ofNat] at this

theorem counter_dec (c : Nat) (hc : c + 1 < 2^64) :
    BitVec.ofNat 64 (c + 1) + signExtend12 4095 = BitVec.ofNat 64 c := by
  rw [signForty095]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_allOnes,
    Nat.mod_eq_of_lt hc]
  have hsum : c + 1 + (2^64 - 1) = c + 2^64 := by omega
  rw [hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
    Nat.mod_eq_of_lt (by omega)]

theorem loop_empty (head : Word) :
    cpsTripleWithin 2 head ((head + 4) + signExtend21 loopExitOffset)
      (CodeReq.ofProg head loop)
      ((.x13 ↦ᵣ 0) ** (.x0 ↦ᵣ 0))
      ((.x13 ↦ᵣ 0) ** (.x0 ↦ᵣ 0)) := by
  exact cpsTripleWithin_extend_code (loop_has_guard_block head) (loopGuard_exit head)

theorem signExtend13_twelve : signExtend13 (BitVec.ofNat 13 12) = (12 : Word) := by
  simp only [signExtend13]
  bv_decide

theorem signExtend21_eight : signExtend21 (BitVec.ofNat 21 8) = (8 : Word) := by
  simp only [signExtend21]
  bv_decide

end ClAsm.Aggregate
