import ClAsm.Aggregate.Correctness
import ClAsm.Aggregate.LoopProof
import ClAsm.Progress.Correctness

namespace ClAsm.Progress

open RiscvZkvm.Rv64 ClAsm.Aggregate

/-- The loop guard falls through to the exit when the counter is zero. -/
theorem rotLoopGuard_exit (head : Word) :
    cpsTripleWithin 2 head ((head + 4) + signExtend21 rotExitOffset)
      (CodeReq.ofProg head rotGuard)
      ((.x13 ↦ᵣ 0) ** (.x0 ↦ᵣ 0))
      ((.x13 ↦ᵣ 0) ** (.x0 ↦ᵣ 0)) := by
  unfold rotGuard
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  have branch := bne_spec_within .x13 .x0 8 0 0 head
  have fallen := cpsBranchWithin_ntakenStripPure2 branch (by
    intro _ h
    rcases h with ⟨_, _, _, _, _, hrest⟩
    rcases hrest with ⟨_, _, _, _, _, hpure⟩
    rcases hpure with ⟨_, hfalse⟩
    exact absurd rfl hfalse)
  have jump := cpsTripleWithin_frameR ((.x13 ↦ᵣ 0) ** (.x0 ↦ᵣ 0)) (by pcFree)
    (jal_x0_spec_gen_within rotExitOffset (head + 4))
  simp only [sepConj_emp_left'] at jump
  have hd : CodeReq.Disjoint (CodeReq.singleton head (.BNE .x13 .x0 8))
      (CodeReq.singleton (head + 4) (.JAL .x0 rotExitOffset)) := by
    intro addr
    by_cases h : addr = head
    · right
      subst h
      simp [CodeReq.singleton]
    · left
      simp [CodeReq.singleton, h]
  have exited := cpsTripleWithin_seq hd fallen jump
  simpa [CodeReq.union_empty_right] using exited

/-- The loop guard jumps the body when the counter is nonzero. -/
theorem rotLoopGuard_taken (head counter : Word) (hneq : counter ≠ 0) :
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

/-- The back jump returns to the guard. -/
theorem rotBackJump_spec (head : Word) :
    cpsTripleWithin 1 (head + 32) head (CodeReq.singleton (head + 32) (.JAL .x0 rotBackOffset))
      empAssertion empAssertion := by
  have jump := jal_x0_spec_gen_within rotBackOffset (head + 32)
  have htarget : (head + 32) + signExtend21 rotBackOffset = head := by
    have h := rotBackTarget (head + 32) head rfl
    simpa using h
  rw [htarget] at jump
  exact jump

theorem rotLoop_has_guard (head : Word) :
    ∀ a i, (CodeReq.singleton head (.BNE .x13 .x0 8)) a = some i →
      (CodeReq.ofProg head rotLoop) a = some i := by
  intro a i h
  have hsub := CodeReq.ofProg_mono_sub head head rotLoop [.BNE .x13 .x0 8] 0
    (by rw [BitVec.add_zero]) (by decide) (by decide) (by decide) a i
  simpa [CodeReq.ofProg_singleton] using hsub h

theorem rotLoop_has_body (head : Word) :
    ∀ a i, (CodeReq.ofProg (head + 8) rotBody) a = some i →
      (CodeReq.ofProg head rotLoop) a = some i := by
  have hsub := CodeReq.ofProg_mono_sub head (head + 8) rotLoop rotBody 2
    (by rfl) (by decide) (by decide) (by decide)
  exact hsub

theorem rotLoop_has_back (head : Word) :
    ∀ a i, (CodeReq.singleton (head + 32) (.JAL .x0 rotBackOffset)) a = some i →
      (CodeReq.ofProg head rotLoop) a = some i := by
  intro a i h
  have hsub := CodeReq.ofProg_mono_sub head (head + 32) rotLoop [.JAL .x0 rotBackOffset] 8
    (by rfl) (by decide) (by decide) (by decide) a i
  simpa [CodeReq.ofProg_singleton] using hsub h

set_option maxHeartbeats 4000000 in
/-- The loop body: load the current flag, store it into the previous slot,
    clear the current slot, and advance both pointers and the counter. -/
theorem rotBody_spec (head prevPtr currPtr counter t5 pf cf : Word) (hneq : counter ≠ 0) :
    cpsTripleWithin 6 (head + 8) (head + 32) (CodeReq.ofProg (head + 8) rotBody)
      ((.x5 ↦ᵣ t5) ** (.x0 ↦ᵣ 0) ** (.x13 ↦ᵣ counter) ** (.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) **
        ((currPtr + signExtend12 0) ↦ₘ cf) ** ((prevPtr + signExtend12 0) ↦ₘ pf))
      ((.x5 ↦ᵣ cf) ** (.x0 ↦ᵣ 0) ** (.x13 ↦ᵣ counter + signExtend12 4095) **
        (.x11 ↦ᵣ prevPtr + signExtend12 8) ** (.x12 ↦ᵣ currPtr + signExtend12 8) **
        ((prevPtr + signExtend12 0) ↦ₘ cf) ** ((currPtr + signExtend12 0) ↦ₘ 0)) := by
  have w0 := ld_spec_within .x5 .x12 currPtr t5 cf 0 (head + 4 * 1) (by decide)
  rw [← CodeReq.ofProg_singleton] at w0
  have e0 := ClAsm.Aggregate.extendBlock (base := head + 8) (whole := rotBody)
    (index := 0) (ha := by simp) (hs := by simp [rotBody]) (hr := by decide) (hsize := by decide) w0
  have w1 := sd_spec_within .x11 .x5 prevPtr pf cf 0 (head + 4 * 2)
  rw [← CodeReq.ofProg_singleton] at w1
  have e1 := ClAsm.Aggregate.extendBlock (base := head + 8) (whole := rotBody) 1 (by simp)
    (by decide) (by decide) (by decide) w1
  have w2 := sd_spec_within .x12 .x0 currPtr 0 cf 0 (head + 4 * 3)
  rw [← CodeReq.ofProg_singleton] at w2
  have e2 := ClAsm.Aggregate.extendBlock (base := head + 8) (whole := rotBody) 2 (by simp)
    (by decide) (by decide) (by decide) w2
  have w3 := addi_spec_within .x11 .x11 prevPtr prevPtr 8 (head + 4 * 4) (by decide)
  rw [← CodeReq.ofProg_singleton] at w3
  have e3 := ClAsm.Aggregate.extendBlock (base := head + 8) (whole := rotBody) 3 (by simp)
    (by decide) (by decide) (by decide) w3
  have w4 := addi_spec_within .x12 .x12 currPtr currPtr 8 (head + 4 * 5) (by decide)
  rw [← CodeReq.ofProg_singleton] at w4
  have e4 := ClAsm.Aggregate.extendBlock (base := head + 8) (whole := rotBody) 4 (by simp)
    (by decide) (by decide) (by decide) w4
  have w5 := addi_spec_within .x13 .x13 counter (counter + signExtend12 4095) 4095
    (head + 4 * 6) (by decide)
  rw [← CodeReq.ofProg_singleton] at w5
  have e5 := ClAsm.Aggregate.extendBlock (base := head + 8) (whole := rotBody) 5 (by simp)
    (by decide) (by decide) (by decide) w5
  seqFrame e0 e1
  seqFrame e0e1 e2
  seqFrame e0e1e2 e3
  seqFrame e0e1e2e3 e4
  seqFrame e0e1e2e3e4 e5
  first
    | exact e0e1e2e3e4e5
    | simpa [sepConj_assoc'] using e0e1e2e3e4e5

set_option maxHeartbeats 4000000 in
/-- One full loop iteration from the guard, through the body, back to the guard. -/
theorem rotIter (head prevPtr currPtr counter pf cf : Word) (hneq : counter ≠ 0) :
    cpsTripleWithin 9 head head (CodeReq.ofProg head rotLoop)
      ((.x13 ↦ᵣ counter) ** (.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) ** (.x0 ↦ᵣ 0) **
        ((prevPtr + signExtend12 0) ↦ₘ pf) ** ((currPtr + signExtend12 0) ↦ₘ cf))
      ((.x13 ↦ᵣ counter + signExtend12 4095) ** (.x11 ↦ᵣ prevPtr + signExtend12 8) **
        (.x12 ↦ᵣ currPtr + signExtend12 8) ** (.x0 ↦ᵣ 0) ** (.x5 ↦ᵣ cf) **
        ((prevPtr + signExtend12 0) ↦ₘ cf) ** ((currPtr + signExtend12 0) ↦ₘ 0)) := by
  have guard := cpsTripleWithin_extend_code (rotLoop_has_guard head)
    (cpsTripleWithin_frameR ((.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) **
      ((prevPtr + signExtend12 0) ↦ₘ pf) ** ((currPtr + signExtend12 0) ↦ₘ cf)) (by pcFree)
      (rotLoopGuard_taken head counter hneq))
  have body := cpsTripleWithin_extend_code (rotLoop_has_body head)
    (rotBody_spec head prevPtr currPtr counter 0 pf cf hneq)
  have back := cpsTripleWithin_extend_code (rotLoop_has_back head) (rotBackJump_spec head)
  seqFrame guard body
  seqFrame guardbody back

end ClAsm.Progress
