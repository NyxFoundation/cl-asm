import ClAsm.Aggregate.Correctness
import RiscvZkvm.Rv64.Logic.BitAux

namespace ClAsm.Aggregate

open RiscvZkvm.Rv64

theorem extendBlock {n : Nat} {base entry exit : Word} {whole block : Program}
    {P Q : Assertion} (index : Nat)
    (ha : entry = base + BitVec.ofNat 64 (4 * index))
    (hs : (whole.drop index).take block.length = block)
    (hr : index + block.length ≤ whole.length) (hsize : 4 * whole.length < 2^64)
    (spec : cpsTripleWithin n entry exit (CodeReq.ofProg entry block) P Q) :
    cpsTripleWithin n entry exit (CodeReq.ofProg base whole) P Q :=
  cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base entry whole block index ha hs hr hsize) spec

def floorBit (value : Word) : Word := if BitVec.ult value incrementWord then 1 else 0

def floorWord (value : Word) : Word :=
  if BitVec.ult value incrementWord then incrementWord else value

theorem floorWord_spec (n : Nat) (hn : n < 2^64) :
    floorWord (BitVec.ofNat 64 n) = BitVec.ofNat 64 (saturateIncrement n) := by
  have hinc : incrementWord.toNat = effectiveBalanceIncrement := by decide
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  unfold floorWord saturateIncrement
  rw [Nat.max_eq_max]
  by_cases h : n < effectiveBalanceIncrement
  · rw [if_pos (by simpa only [BitVec.ult_iff_toNat_lt, hn', hinc] using h),
      Nat.max_eq_left (by omega)]
    rfl
  · rw [if_neg (by simpa only [BitVec.ult_iff_toNat_lt, hn', hinc] using h),
      Nat.max_eq_right (by omega)]

theorem floorBranch_spec (base flag : Word) :
    cpsTripleWithin 1 base (if flag = 0 then base + 4 else base + 12)
      (CodeReq.singleton base (.BNE .x5 .x0 12))
      ((.x5 ↦ᵣ flag) ** (.x0 ↦ᵣ 0)) ((.x5 ↦ᵣ flag) ** (.x0 ↦ᵣ 0)) := by
  have branch := bne_spec_within .x5 .x0 12 flag 0 base
  by_cases h : flag = 0
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
    rw [show signExtend13 (12 : BitVec 13) = (12 : Word) by decide] at taken
    exact taken

set_option maxHeartbeats 2000000 in
theorem saturateOne_spec (reg : Reg) (offset : BitVec 12)
    (base scratch value old temp : Word) :
    cpsTripleWithin 4 base (base + 20) (CodeReq.ofProg base (saturateOne reg offset))
      ((.x0 ↦ᵣ 0) ** (.x5 ↦ᵣ temp) ** (reg ↦ᵣ value) **
        (.x28 ↦ᵣ incrementWord) ** (.x15 ↦ᵣ scratch) **
        ((scratch + signExtend12 offset) ↦ₘ old))
      ((.x0 ↦ᵣ 0) ** (.x5 ↦ᵣ floorBit value) ** (reg ↦ᵣ value) **
        (.x28 ↦ᵣ incrementWord) ** (.x15 ↦ᵣ scratch) **
        ((scratch + signExtend12 offset) ↦ₘ floorWord value)) := by
  have s0 := sltu_spec_gen_within .x5 reg .x28 temp value incrementWord base (by decide)
  have s1 := floorBranch_spec (base + 4) (floorBit value)
  have s2 := sd_spec_within .x15 reg scratch value old offset (base + 8)
  have s3 := jal_x0_spec_gen_within 8 (base + 12)
  have s4 := sd_spec_within .x15 .x28 scratch incrementWord old offset (base + 16)
  rw [← CodeReq.ofProg_singleton] at s0 s1 s2 s3 s4
  have s0 := extendBlock (base := base) (whole := saturateOne reg offset) 0 (by simp) (by rfl)
    (by simp [saturateOne, if_eq]) (by simp [saturateOne, if_eq]) s0
  have s1 := extendBlock (base := base) (whole := saturateOne reg offset) 1 rfl (by rfl)
    (by simp [saturateOne, if_eq]) (by simp [saturateOne, if_eq]) s1
  have s2 := extendBlock (base := base) (whole := saturateOne reg offset) 2 rfl (by rfl)
    (by simp [saturateOne, if_eq]) (by simp [saturateOne, if_eq]) s2
  have s3 := extendBlock (base := base) (whole := saturateOne reg offset) 3 rfl (by rfl)
    (by simp [saturateOne, if_eq]) (by simp [saturateOne, if_eq]) s3
  have s4 := extendBlock (base := base) (whole := saturateOne reg offset) 4 rfl (by rfl)
    (by simp [saturateOne, if_eq]) (by simp [saturateOne, if_eq]) s4
  generalize hcode : CodeReq.ofProg base (saturateOne reg offset) = code at s0 s1 s2 s3 s4 ⊢
  by_cases h : BitVec.ult value incrementWord
  · simp only [floorBit, floorWord, if_pos h] at s0 s1 ⊢
    simp only [show ¬((1 : Word) = 0) by decide, if_false] at s1
    apply cpsTripleWithin_mono_nSteps (nSteps := 3) (by decide)
    runBlock s0 s1 s4
  · simp only [floorBit, floorWord, if_neg h, if_true] at s0 s1 ⊢
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) by decide] at s3
    runBlock s0 s1 s2 s3

theorem return_spec (base ret : Word) (hret : ret &&& 1 = 0) :
    cpsTripleWithin 1 base ret (CodeReq.singleton base (.JALR .x0 .x1 0))
      (.x1 ↦ᵣ ret) (.x1 ↦ᵣ ret) := by
  have jump := jalr_x0_spec_gen_within .x1 ret 0 base
  have target : (ret + signExtend12 0) &&& ~~~(1 : Word) = ret := by
    simpa [signExtend12] using BitAux.word_andn_one_of_even hret
  rw [target] at jump
  exact jump

set_option maxHeartbeats 2000000 in
theorem epilogue_spec (base scratch ret total prev curr oldT oldP oldC temp : Word)
    (hret : ret &&& 1 = 0) :
    cpsTripleWithin 13 base ret (CodeReq.ofProg base epilogue)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ret) ** (.x5 ↦ᵣ temp) ** (.x15 ↦ᵣ scratch) **
        (.x17 ↦ᵣ total) ** (.x28 ↦ᵣ incrementWord) ** (.x29 ↦ᵣ prev) ** (.x30 ↦ᵣ curr) **
        ((scratch + signExtend12 0) ↦ₘ oldT) ** ((scratch + signExtend12 8) ↦ₘ oldP) **
        ((scratch + signExtend12 16) ↦ₘ oldC))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ret) ** (.x5 ↦ᵣ floorBit curr) ** (.x15 ↦ᵣ scratch) **
        (.x17 ↦ᵣ total) ** (.x28 ↦ᵣ incrementWord) ** (.x29 ↦ᵣ prev) ** (.x30 ↦ᵣ curr) **
        ((scratch + signExtend12 0) ↦ₘ floorWord total) **
        ((scratch + signExtend12 8) ↦ₘ floorWord prev) **
        ((scratch + signExtend12 16) ↦ₘ floorWord curr)) := by
  have s0 := saturateOne_spec .x17 0 base scratch total oldT temp
  have s1 := saturateOne_spec .x29 8 (base + 20) scratch prev oldP (floorBit total)
  have s2 := saturateOne_spec .x30 16 (base + 40) scratch curr oldC (floorBit prev)
  have s3 := return_spec (base + 60) ret hret
  rw [← CodeReq.ofProg_singleton] at s3
  have s0 := extendBlock (base := base) (whole := epilogue) 0 (by simp) (by decide) (by decide) (by decide) s0
  have s1 := extendBlock (base := base) (whole := epilogue) 5 rfl (by decide) (by decide) (by decide) s1
  have s2 := extendBlock (base := base) (whole := epilogue) 10 rfl (by decide) (by decide) (by decide) s2
  have s3 := extendBlock (base := base) (whole := epilogue) 15 rfl (by decide) (by decide) (by decide) s3
  generalize hcode : CodeReq.ofProg base epilogue = code at s0 s1 s2 s3 ⊢
  runBlock s0 s1 s2 s3

end ClAsm.Aggregate
