import ClAsm.Aggregate.Epilogue
import ClAsm.Aggregate.Loop
import ClAsm.Aggregate.LoopProof
import ClAsm.Progress.Layout
import ClAsm.Progress.Program
import ClAsm.Progress.State

namespace ClAsm.Progress

open RiscvZkvm.Rv64 ClAsm.Aggregate

theorem fiveShift : (5 : BitVec 6).toNat = 5 := by decide

theorem signExtend13_eight : signExtend13 (8 : BitVec 13) = (8 : Word) := by
  simp only [signExtend13]
  bv_decide

theorem eth1Branch_spec (base : Word) (val : Word) :
    cpsTripleWithin 1 base (if val = 0 then (base + 4) else (base + 8))
      (CodeReq.singleton base (.BNE .x17 .x0 8))
      ((.x17 ↦ᵣ val) ** (.x0 ↦ᵣ 0)) ((.x17 ↦ᵣ val) ** (.x0 ↦ᵣ 0)) := by
  have branch := bne_spec_within .x17 .x0 8 val 0 base
  by_cases h : val = 0
  · rw [if_pos h]
    exact cpsBranchWithin_ntakenStripPure2 branch (by
      intro _ hp
      rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, hpure⟩
      exact hpure h)
  · rw [if_neg h]
    have taken := cpsBranchWithin_takenStripPure2 branch (by
      intro _ hp
      rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, hpure⟩
      exact h hpure)
    rw [signExtend13_eight] at taken
    exact taken

theorem eth1Lui_cell :
    (((0x74000 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 = (0x74000000 : Word) := by
  rfl

theorem slashingsLui_cell :
    (((0x73000 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 = (0x73000000 : Word) := by
  rfl

theorem randaoLui_cell :
    (((0x72000 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 = (0x72000000 : Word) := by
  rfl

theorem previousLui_cell :
    (((0x70000 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 = (0x70000000 : Word) := by
  rfl

theorem currentLui_cell :
    (((0x71000 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 = (0x71000000 : Word) := by
  rfl

theorem mask8191 :
    (((2 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 + signExtend12 4095
      = (8191 : Word) := by
  simp only [signExtend12]
  bv_decide

theorem mask65535 :
    (((0x10 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 + signExtend12 4095
      = (65535 : Word) := by
  simp only [signExtend12]
  bv_decide

abbrev slashTarget (epoch cell : Word) : Word :=
  (((epoch + signExtend12 1) &&& 8191) <<< (3 : Nat)) + cell

abbrev randaoCurrAddr (epoch cell : Word) : Word :=
  (epoch &&& 65535) <<< (3 : Nat) + cell

abbrev randaoNextAddr (epoch cell : Word) : Word :=
  ((epoch + signExtend12 1) &&& 65535) <<< (3 : Nat) + cell

set_option maxHeartbeats 4000000 in
theorem eth1Reset_spec (base cell slot t16 t17 t18 old : Word)
    (hcell : (((0x74000 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 = cell) :
    cpsTripleWithin 6 base (base + 24) (CodeReq.ofProg base eth1Reset)
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ slot) ** (.x16 ↦ᵣ t16) ** (.x17 ↦ᵣ t17) **
        (.x18 ↦ᵣ t18) ** (cell ↦ₘ old))
      ((.x0 ↦ᵣ 0) ** (.x14 ↦ᵣ slot) ** (.x16 ↦ᵣ (slot >>> 5)) **
        (.x17 ↦ᵣ ((slot >>> 5) + signExtend12 1) &&& 63) ** (.x18 ↦ᵣ cell) **
        (cell ↦ₘ
          if ((slot >>> 5) + signExtend12 1) &&& 63 = 0 then 0 else old)) := by
  have p0 := srli_spec_gen_within .x16 .x14 t16 slot (5 : BitVec 6) base (by decide)
  rw [fiveShift] at p0
  have p1 := addi_spec_within .x17 .x16 (slot >>> 5) t17 1 (base + 4 * 1) (by decide)
  have p2 := andi_spec_gen_same_within .x17 ((slot >>> 5) + signExtend12 1) 63 (base + 4 * 2) (by decide)
  have p3 := lui_spec_within .x18 t18 (0x74000 : BitVec 20) (base + 4 * 3) (by decide)
  have p4 := eth1Branch_spec (base + 4 * 4) (((slot >>> 5) + signExtend12 1) &&& 63)
  have p5 := sd_spec_within .x18 .x0 cell 0 old 0 (base + 4 * 5)
  rw [← CodeReq.ofProg_singleton] at p0 p1 p2 p3 p4 p5
  rw [hcell] at p3
  have p0 := ClAsm.Aggregate.extendBlock (base := base) (whole := eth1Reset) 0 (by simp)
    (by simp [eth1Reset]) (by decide) (by simp [eth1Reset]) p0
  have p1 := ClAsm.Aggregate.extendBlock (base := base) (whole := eth1Reset) 1 (by simp)
    (by simp [eth1Reset]) (by decide) (by simp [eth1Reset]) p1
  have p2 := ClAsm.Aggregate.extendBlock (base := base) (whole := eth1Reset) 2 (by simp)
    (by simp [eth1Reset]) (by decide) (by simp [eth1Reset]) p2
  have p3 := ClAsm.Aggregate.extendBlock (base := base) (whole := eth1Reset) 3 (by simp)
    (by simp [eth1Reset]) (by decide) (by simp [eth1Reset]) p3
  have p4 := ClAsm.Aggregate.extendBlock (base := base) (whole := eth1Reset) 4 (by simp)
    (by simp [eth1Reset]) (by decide) (by simp [eth1Reset]) p4
  have p5 := ClAsm.Aggregate.extendBlock (base := base) (whole := eth1Reset) 5 (by simp)
    (by simp [eth1Reset]) (by decide) (by simp [eth1Reset]) p5
  generalize hcode : CodeReq.ofProg base eth1Reset = code at p0 p1 p2 p3 p4 p5 ⊢
  by_cases h : ((slot >>> 5) + signExtend12 1) &&& 63 = 0
  · rw [if_pos h] at p4
    simp only [if_pos h] at p5 ⊢
    runBlock p0 p1 p2 p3 p4 p5
  · rw [if_neg h] at p4
    have hif : (if (((slot >>> 5) + signExtend12 1) &&& 63 = 0) then (0 : Word) else old) = old :=
      if_neg h
    simp only [hif] at p5 ⊢
    apply cpsTripleWithin_mono_nSteps (nSteps := 5) (by decide)
    runBlock p0 p1 p2 p3 p4

set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
theorem slashingsReset_spec (base cell epoch t17 t18 t19 old : Word)
    (hcell : (((0x73000 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 = cell) :
    cpsTripleWithin 8 base (base + 32) (CodeReq.ofProg base slashingsReset)
      ((.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ t17) ** (.x0 ↦ᵣ 0) ** (.x18 ↦ᵣ t18) ** (.x19 ↦ᵣ t19) **
        ((cell + signExtend12 0) ↦ₘ old) ** ((slashTarget epoch cell + signExtend12 0) ↦ₘ old))
      ((.x17 ↦ᵣ slashTarget epoch cell) ** (.x0 ↦ᵣ 0) ** ((slashTarget epoch cell + signExtend12 0) ↦ₘ 0) **
        (.x16 ↦ᵣ epoch) ** (.x18 ↦ᵣ 8191) ** (.x19 ↦ᵣ cell) ** ((cell + signExtend12 0) ↦ₘ old)) := by
  have u0 := addi_spec_within .x17 .x16 epoch t17 1 base (by decide)
  have u1 := lui_spec_within .x18 t18 (2 : BitVec 20) (base + 4) (by decide)
  have u2 : cpsTripleWithin 1 ((base + 4) + 4) (((base + 4) + 4) + 4)
      (CodeReq.ofProg ((base + 4) + 4) [.ADDI .x18 .x18 4095])
      (.x18 ↦ᵣ (((2 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64)
      (.x18 ↦ᵣ (((2 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 + signExtend12 4095) :=
    addi_spec_same_within .x18 _ 4095 ((base + 4) + 4) (by decide)
  rw [show ((base + 4) + 4) + 4 = base + 12 by bv_omega] at u2
  rw [show ((base + 4) + 4) = base + 4 * 2 by bv_omega] at u2
  rw [mask8191] at u2
  have u3 := and_spec_gen_rd_eq_rs1_within .x17 .x18 (epoch + signExtend12 1) 8191
    (base + 12) (by decide)
  have u4 := slli_spec_gen_same_within .x17
    ((epoch + signExtend12 1) &&& 8191) (3 : BitVec 6) (base + 16) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 by decide] at u4
  have u5 := lui_spec_within .x19 t19 (0x73000 : BitVec 20) (base + 20) (by decide)
  rw [hcell] at u5
  have u6 := add_spec_gen_rd_eq_rs1_within .x17 .x19
    (((epoch + signExtend12 1) &&& 8191) <<< 3) cell (base + 24) (by decide)
  have u7 := sd_spec_within .x17 .x0 (slashTarget epoch cell) 0 old 0 (base + 28)
  rw [← CodeReq.ofProg_singleton] at u0 u1 u3 u4 u5 u6 u7
  rw [show (base + 4) + 4 = base + 4 * 2 by bv_omega] at u1
  rw [show (base + 12) + 4 = base + 4 * 4 by bv_omega] at u3
  rw [show (base + 16) + 4 = base + 4 * 5 by bv_omega] at u4
  rw [show (base + 20) + 4 = base + 4 * 6 by bv_omega] at u5
  rw [show (base + 24) + 4 = base + 4 * 7 by bv_omega] at u6
  -- Carry the untouched registers and cell through every piece.
  have c0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x18 ↦ᵣ t18) ** (.x19 ↦ᵣ t19) **
    ((cell + signExtend12 0) ↦ₘ old) ** ((slashTarget epoch cell + signExtend12 0) ↦ₘ old)) (by pcFree) u0
  have c1 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ epoch + signExtend12 1) **
    (.x19 ↦ᵣ t19) ** ((cell + signExtend12 0) ↦ₘ old) ** ((slashTarget epoch cell + signExtend12 0) ↦ₘ old))
    (by pcFree) u1
  have c2 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ epoch + signExtend12 1) **
    (.x19 ↦ᵣ t19) ** ((cell + signExtend12 0) ↦ₘ old) ** ((slashTarget epoch cell + signExtend12 0) ↦ₘ old))
    (by pcFree) u2
  have c3 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) ** (.x19 ↦ᵣ t19) **
    ((cell + signExtend12 0) ↦ₘ old) ** ((slashTarget epoch cell + signExtend12 0) ↦ₘ old)) (by pcFree) u3
  have c4 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) ** (.x18 ↦ᵣ 8191) **
    (.x19 ↦ᵣ t19) ** ((cell + signExtend12 0) ↦ₘ old) ** ((slashTarget epoch cell + signExtend12 0) ↦ₘ old))
    (by pcFree) u4
  have c5 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ
    ((epoch + signExtend12 1) &&& 8191) <<< 3) ** (.x18 ↦ᵣ 8191) ** ((cell + signExtend12 0) ↦ₘ old) **
    ((slashTarget epoch cell + signExtend12 0) ↦ₘ old)) (by pcFree) u5
  have c6 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) ** (.x18 ↦ᵣ 8191) **
    ((cell + signExtend12 0) ↦ₘ old) ** ((slashTarget epoch cell + signExtend12 0) ↦ₘ old)) (by pcFree) u6
  have c7 := cpsTripleWithin_frameR ((.x16 ↦ᵣ epoch) ** (.x18 ↦ᵣ 8191) ** (.x19 ↦ᵣ cell) **
    ((cell + signExtend12 0) ↦ₘ old)) (by pcFree) u7
  generalize hcode : CodeReq.ofProg base slashingsReset = code at c0 c1 c2 c3 c4 c5 c6 c7 ⊢
  have e0 := ClAsm.Aggregate.extendBlock (base := base) (whole := slashingsReset) 0 (by simp)
    (by decide) (by decide) (by decide) c0
  have e1 := ClAsm.Aggregate.extendBlock (base := base) (whole := slashingsReset) 1 rfl
    (by decide) (by decide) (by decide) c1
  have e2 := ClAsm.Aggregate.extendBlock (base := base) (whole := slashingsReset) 2 (by bv_omega)
    (by decide) (by decide) (by decide) c2
  have e3 := ClAsm.Aggregate.extendBlock (base := base) (whole := slashingsReset) 3 rfl
    (by decide) (by decide) (by decide) c3
  have e4 := ClAsm.Aggregate.extendBlock (base := base) (whole := slashingsReset) 4 rfl
    (by decide) (by decide) (by decide) c4
  have e5 := ClAsm.Aggregate.extendBlock (base := base) (whole := slashingsReset) 5 rfl
    (by decide) (by decide) (by decide) c5
  have e6 := ClAsm.Aggregate.extendBlock (base := base) (whole := slashingsReset) 6 rfl
    (by decide) (by decide) (by decide) c6
  have e7 := ClAsm.Aggregate.extendBlock (base := base) (whole := slashingsReset) 7 rfl
    (by decide) (by decide) (by decide) c7
  seqFrame e0 e1
  seqFrame e0e1 e2
  seqFrame e0e1e2 e3
  seqFrame e0e1e2e3 e4
  seqFrame e0e1e2e3e4 e5
  seqFrame e0e1e2e3e4e5 e6
  seqFrame e0e1e2e3e4e5e6 e7
  rw [show (base + 28) + 4 = base + 32 by bv_omega] at e0e1e2e3e4e5e6e7
  rw [hcode] at e0e1e2e3e4e5e6e7
  have hsteps : (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = (8 : Nat) := by rfl
  rw [hsteps] at e0e1e2e3e4e5e6e7
  first
    | exact e0e1e2e3e4e5e6e7
    | simpa [sepConj_assoc'] using e0e1e2e3e4e5e6e7


set_option maxHeartbeats 4000000 in
theorem randaoReset_spec (base cell epoch t5 t15 t17 t18 t19 t20 oldMix mixNext : Word)
    (hcell : (((0x72000 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 = cell) :
    cpsTripleWithin 13 base (base + 52) (CodeReq.ofProg base randaoReset)
      ((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ t5) ** (.x17 ↦ᵣ t17) **
        (.x18 ↦ᵣ t18) ** (.x19 ↦ᵣ t19) ** (.x20 ↦ᵣ t20) **
        ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
        ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext))
      ((.x20 ↦ᵣ randaoNextAddr epoch cell) ** (.x5 ↦ᵣ oldMix) **
        ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
        (.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x17 ↦ᵣ randaoCurrAddr epoch cell) **
        (.x18 ↦ᵣ 65535) ** (.x19 ↦ᵣ cell) **
        ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix)) := by
  have v0 := lui_spec_within .x18 t18 (0x10 : BitVec 20) base (by decide)
  have v1 : cpsTripleWithin 1 (base + 4 * 1) ((base + 4 * 1) + 4)
      (CodeReq.ofProg (base + 4 * 1) [.ADDI .x18 .x18 4095])
      (.x18 ↦ᵣ (((0x10 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64)
      (.x18 ↦ᵣ (((0x10 : BitVec 20).zeroExtend 32) <<< 12).signExtend 64 + signExtend12 4095) :=
    addi_spec_same_within .x18 _ 4095 (base + 4 * 1) (by decide)
  rw [show ((base + 4 * 1) + 4) = base + 4 * 2 by bv_omega] at v1
  rw [mask65535] at v1
  have v2 := addi_spec_within .x17 .x16 epoch t17 0 (base + 4 * 2) (by decide)
  have v3 := and_spec_gen_rd_eq_rs1_within .x17 .x18 epoch 65535
    (base + 4 * 3) (by decide)
  have v4 := slli_spec_gen_same_within .x17 (epoch &&& 65535) (3 : BitVec 6) (base + 4 * 4) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 by decide] at v4
  have v5 := lui_spec_within .x19 t19 (0x72000 : BitVec 20) (base + 4 * 5) (by decide)
  rw [hcell] at v5
  have v6 := add_spec_gen_rd_eq_rs1_within .x17 .x19 ((epoch &&& 65535) <<< 3) cell
    (base + 4 * 6) (by decide)
  have v7 := ld_spec_within .x5 .x17 (randaoCurrAddr epoch cell) t5 oldMix 0
    (base + 4 * 7) (by decide)
  have v8 := addi_spec_within .x20 .x16 epoch t20 1 (base + 4 * 8) (by decide)
  have v9 := and_spec_gen_rd_eq_rs1_within .x20 .x18 (epoch + signExtend12 1) 65535
    (base + 4 * 9) (by decide)
  have v10 := slli_spec_gen_same_within .x20 ((epoch + signExtend12 1) &&& 65535)
    (3 : BitVec 6) (base + 4 * 10) (by decide)
  rw [show (3 : BitVec 6).toNat = 3 by decide] at v10
  have v11 := add_spec_gen_rd_eq_rs1_within .x20 .x19
    (((epoch + signExtend12 1) &&& 65535) <<< 3) cell (base + 4 * 11) (by decide)
  have v12 := sd_spec_within .x20 .x5 (randaoNextAddr epoch cell) oldMix mixNext 0
    (base + 4 * 12)
  rw [← CodeReq.ofProg_singleton] at v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12

  -- Carry the untouched registers and cells through every piece.
  have f0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ t5) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ t17) **
    (.x19 ↦ᵣ t19) ** (.x20 ↦ᵣ t20) ** ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v0
  have f1 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ t5) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ t17) **
    (.x19 ↦ᵣ t19) ** (.x20 ↦ᵣ t20) ** ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v1
  have f2 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ t5) ** (.x17 ↦ᵣ t17) ** (.x18 ↦ᵣ 65535) **
    (.x19 ↦ᵣ t19) ** (.x20 ↦ᵣ t20) ** ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v2
  have f3 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ t5) ** (.x16 ↦ᵣ epoch) ** (.x19 ↦ᵣ t19) ** (.x20 ↦ᵣ t20) **
    ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v3
  have f4 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ t5) ** (.x16 ↦ᵣ epoch) ** (.x18 ↦ᵣ 65535) **
    (.x19 ↦ᵣ t19) ** (.x20 ↦ᵣ t20) ** ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v4
  have f5 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ t5) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ randaoCurrAddr epoch cell) ** (.x18 ↦ᵣ 65535) ** (.x20 ↦ᵣ t20) **
    ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v5
  have f6 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ t5) ** (.x16 ↦ᵣ epoch) ** (.x18 ↦ᵣ 65535) ** (.x20 ↦ᵣ t20) **
    ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v6
  have f7 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x16 ↦ᵣ epoch) ** (.x18 ↦ᵣ 65535) ** (.x19 ↦ᵣ cell) ** (.x20 ↦ᵣ t20) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v7
  have f8 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x17 ↦ᵣ randaoCurrAddr epoch cell) ** (.x18 ↦ᵣ 65535) ** (.x19 ↦ᵣ cell) **
    ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v8
  have f9 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ oldMix) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ randaoCurrAddr epoch cell) ** (.x19 ↦ᵣ cell) **
    ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v9
  have f10 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ oldMix) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ randaoCurrAddr epoch cell) ** (.x18 ↦ᵣ 65535) ** (.x19 ↦ᵣ cell) **
    ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v10
  have f11 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x5 ↦ᵣ oldMix) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ randaoCurrAddr epoch cell) ** (.x18 ↦ᵣ 65535) **
    ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix) **
    ((randaoNextAddr epoch cell + signExtend12 0) ↦ₘ mixNext)) (by pcFree) v11
  have f12 := cpsTripleWithin_frameR ((.x0 ↦ᵣ 0) ** (.x15 ↦ᵣ t15) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ randaoCurrAddr epoch cell) ** (.x18 ↦ᵣ 65535) ** (.x19 ↦ᵣ cell) **
    ((randaoCurrAddr epoch cell + signExtend12 0) ↦ₘ oldMix)) (by pcFree) v12
  generalize hcode : CodeReq.ofProg base randaoReset = code at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 ⊢
  have g0 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 0 (by simp)
    (by decide) (by decide) (by decide) f0
  have g1 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 1 rfl
    (by decide) (by decide) (by decide) f1
  have g2 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 2 rfl
    (by decide) (by decide) (by decide) f2
  have g3 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 3 rfl
    (by decide) (by decide) (by decide) f3
  have g4 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 4 rfl
    (by decide) (by decide) (by decide) f4
  have g5 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 5 rfl
    (by decide) (by decide) (by decide) f5
  have g6 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 6 rfl
    (by decide) (by decide) (by decide) f6
  have g7 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 7 rfl
    (by decide) (by decide) (by decide) f7
  have g8 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 8 rfl
    (by decide) (by decide) (by decide) f8
  have g9 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 9 rfl
    (by decide) (by decide) (by decide) f9
  have g10 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 10 rfl
    (by decide) (by decide) (by decide) f10
  have g11 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 11 rfl
    (by decide) (by decide) (by decide) f11
  have g12 := ClAsm.Aggregate.extendBlock (base := base) (whole := randaoReset) 12 rfl
    (by decide) (by decide) (by decide) f12
  seqFrame g0 g1
  seqFrame g0g1 g2
  seqFrame g0g1g2 g3
  seqFrame g0g1g2g3 g4
  seqFrame g0g1g2g3g4 g5
  seqFrame g0g1g2g3g4g5 g6
  seqFrame g0g1g2g3g4g5g6 g7
  seqFrame g0g1g2g3g4g5g6g7 g8
  seqFrame g0g1g2g3g4g5g6g7g8 g9
  seqFrame g0g1g2g3g4g5g6g7g8g9 g10
  seqFrame g0g1g2g3g4g5g6g7g8g9g10 g11
  seqFrame g0g1g2g3g4g5g6g7g8g9g10g11 g12
  first
    | exact g0g1g2g3g4g5g6g7g8g9g10g11g12
    | simpa [sepConj_assoc'] using g0g1g2g3g4g5g6g7g8g9g10g11g12

end ClAsm.Progress
