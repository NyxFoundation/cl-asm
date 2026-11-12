import ClAsm.Aggregate.Contract
import ClAsm.Arithmetic.Proof
import ClAsm.EpochAtSlot.Proof
import RiscvZkvm.Rv64.Logic.SyscallSpecs
import RiscvZkvm.Rv64.Logic.Tactics.RunBlock
import RiscvZkvm.Rv64.Logic.Tactics.XPerm
import RiscvZkvm.Rv64.Logic.CPSSpec

namespace ClAsm.Aggregate

open RiscvZkvm.Rv64

/-- Small immediate constants sign-extend to themselves. -/
theorem zeroSign : signExtend12 (0 : BitVec 12) = (0 : Word) := by
  simp only [signExtend12]
  bv_decide

theorem signEight : signExtend12 (8 : BitVec 12) = (8 : Word) := by
  simp only [signExtend12]
  bv_decide

theorem signThirtyTwo : signExtend12 (32 : BitVec 12) = (32 : Word) := by
  simp only [signExtend12]
  bv_decide

theorem oneSign : signExtend12 (1 : BitVec 12) = (1 : Word) := by
  simp only [signExtend12]
  bv_decide

theorem allOnesLit : ((18446744073709551615#64 : Word) = BitVec.allOnes 64) := by
  bv_decide

theorem signForty095 : signExtend12 (4095 : BitVec 12) = BitVec.allOnes 64 := by
  simp only [signExtend12]
  bv_decide

theorem signTwo : signExtend12 (2 : BitVec 12) = (2 : Word) := by
  simp only [signExtend12]
  bv_decide

/-- Adding a bounded Nat to a word, without wrapping. -/
theorem wordAdd (a : Word) (b : Nat) (h : a.toNat + b < 2^64) :
    a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a.toNat + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : b < 2^64)]

theorem wordAddWord (a b : Word) : a + b = BitVec.ofNat 64 (a.toNat + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem wordNat (a : Word) : a = BitVec.ofNat 64 a.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  symm
  exact Nat.mod_eq_of_lt a.isLt

/-- The canonical 0/1 word for a boolean. -/
def bitWord : Bool → Word
  | true => 1
  | false => 0

/-- Complementing a 0/1 word with XORI 1. -/
theorem xori01 (b : Bool) : bitWord b ^^^ signExtend12 (1 : BitVec 12) = bitWord !b := by
  rw [oneSign]
  cases b <;> simp only [bitWord] <;> bv_decide

/-- The AND of two 0/1 words. -/
theorem and01 (a b : Word) (p q : Bool) (ha : a = bitWord p) (hb : b = bitWord q) :
    a &&& b = bitWord (p && q) := by
  cases p <;> cases q <;> simp only [ha, hb, bitWord] <;> bv_decide

/-- Masking corollaries used by the loop body. -/
theorem subOnes : ((0 : Word) - (1 : Word)) = 18446744073709551615#64 := by
  bv_decide

theorem subZero : ((0 : Word) - (0 : Word)) = (0 : Word) := by
  bv_decide

theorem andAllOnesLit (eff : Word) : eff &&& 18446744073709551615#64 = eff := by
  rw [allOnesLit]
  exact (BitVec.and_allOnes (x := eff))

theorem andZeroLit (eff : Word) : eff &&& (0 : Word) = (0 : Word) :=
  BitVec.and_zero (x := eff)

/-- Unslashing a uint8 boolean reproduces the decidable-zero test. -/
theorem unslashedBit (s : Word) (hs : s = 0 ∨ s = 1) :
    (bitWord (BitVec.ult (0 : Word) s)) ^^^ signExtend12 (1 : BitVec 12) = bitWord (s = 0) := by
  cases hs with
  | inl h => subst h; decide
  | inr h => subst h; decide

/-- Adding the machine's selected balance to the running accumulator. -/
theorem activeSelect (acc eff mask : Word) (sel : Bool)
    (hm : eff &&& mask = (if sel then eff else 0))
    (hbound : acc.toNat + (if sel then eff.toNat else 0) < 2^64) :
    acc + (eff &&& mask) = BitVec.ofNat 64 (acc.toNat + (if sel then eff.toNat else 0)) := by
  rw [hm]
  cases sel with
  | true =>
      rw [if_pos (rfl : true = true), if_pos (rfl : true = true)]
      exact wordAddWord acc eff
  | false =>
      rw [if_neg (by decide : ¬(false = true))]
      have hzero : (acc + (0 : Word)) = acc := BitVec.add_zero (x := acc)
      rw [hzero, if_neg (by decide : ¬(false = true)), Nat.add_zero]
      exact wordNat acc

/-- Machine form of `!BitVec.ult epoch activation`. -/
def notBeforeActivation (epoch activation : Word) : Word :=
  (if BitVec.ult epoch activation then (1 : Word) else 0) ^^^ signExtend12 (1 : BitVec 12)

/-- Machine form of `BitVec.ult epoch exit`. -/
def beforeExit (epoch exitEpoch : Word) : Word :=
  if BitVec.ult epoch exitEpoch then (1 : Word) else 0

/-- The 0/1 word `is_active_validator` computes with `SLTU`/`XORI`/`AND`. -/
def activeBit (epoch activation exitEpoch : Word) : Word :=
  beforeExit epoch exitEpoch &&& notBeforeActivation epoch activation

/-- `0 - bit` is the mask that keeps or clears the effective balance. -/
def activeMask (epoch activation exitEpoch : Word) : Word :=
  (0 : Word) - activeBit epoch activation exitEpoch

def selectedEffective (epoch : Word) (validator : Validator) : Word :=
  validator.effectiveBalance &&& activeMask epoch validator.activationEpoch validator.exitEpoch

def foldedActive (acc epoch : Word) (validator : Validator) : Word :=
  acc + selectedEffective epoch validator

set_option maxHeartbeats 2000000 in
theorem activeFold_x16_spec (base ptr epoch acc t5 t6 t7 : Word) (validator : Validator) :
    cpsTripleWithin (activeFold .x16 .x17).length base (base + 40)
      (CodeReq.ofProg base (activeFold .x16 .x17))
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ acc) **
        (.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7) ** validator.owns ptr)
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) **
        (.x17 ↦ᵣ foldedActive acc epoch validator) **
        (.x5 ↦ᵣ activeBit epoch validator.activationEpoch validator.exitEpoch) **
        (.x6 ↦ᵣ selectedEffective epoch validator) **
        (.x7 ↦ᵣ activeMask epoch validator.activationEpoch validator.exitEpoch) **
        validator.owns ptr) := by
  unfold activeFold foldedActive selectedEffective activeMask activeBit
    beforeExit notBeforeActivation Validator.owns
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  let actv := validator.activationEpoch
  let exitv := validator.exitEpoch
  let eff := validator.effectiveBalance
  have s0 := ld_spec_gen_within .x5 .x10 ptr t5 actv 8 base (by decide)
  have s1 := ld_spec_gen_within .x6 .x10 ptr t6 exitv 16 (base + 4) (by decide)
  have s2 := sltu_spec_gen_within .x7 .x16 .x5 t7 epoch actv (base + 8) (by decide)
  have s3 := xori_spec_gen_same_within .x7
    (if BitVec.ult epoch actv then 1 else 0) 1 (base + 12) (by decide)
  have s4 := sltu_spec_gen_within .x5 .x16 .x6 actv epoch exitv (base + 16) (by decide)
  have s5 := and_spec_gen_rd_eq_rs1_within .x5 .x7
    (if BitVec.ult epoch exitv then 1 else 0)
    ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1) (base + 20) (by decide)
  have s6 := ld_spec_gen_within .x6 .x10 ptr exitv eff 0 (base + 24) (by decide)
  have s7 := sub_spec_gen_within .x7 .x0 .x5 0
    ((if BitVec.ult epoch exitv then 1 else 0) &&&
      ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1))
    ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1) (base + 28) (by decide)
  have s8 := and_spec_gen_rd_eq_rs1_within .x6 .x7 eff
    ((0 : Word) - ((if BitVec.ult epoch exitv then 1 else 0) &&&
      ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1))) (base + 32) (by decide)
  have s9 := add_spec_gen_rd_eq_rs1_within .x17 .x6 acc
    (eff &&& ((0 : Word) - ((if BitVec.ult epoch exitv then 1 else 0) &&&
      ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1)))) (base + 36) (by decide)
  runBlock s0 s1 s2 s3 s4 s5 s6 s7 s8 s9

def slashedBit (slashed : Word) : Word :=
  if BitVec.ult (0 : Word) slashed then 1 else 0

def unslashedWord (slashed : Word) : Word :=
  slashedBit slashed ^^^ signExtend12 (1 : BitVec 12)

def flagBit (flags : Word) : Word :=
  if BitVec.ult (0 : Word) (flags &&& signExtend12 (2 : BitVec 12)) then 1 else 0

def targetBit (epoch : Word) (validator : Validator) (flags : Word) : Word :=
  (activeBit epoch validator.activationEpoch validator.exitEpoch &&&
    unslashedWord validator.slashed) &&& flagBit flags

def targetMask (epoch : Word) (validator : Validator) (flags : Word) : Word :=
  (0 : Word) - targetBit epoch validator flags

def selectedTarget (epoch : Word) (validator : Validator) (flags : Word) : Word :=
  validator.effectiveBalance &&& targetMask epoch validator flags

def foldedTarget (acc epoch : Word) (validator : Validator) (flags : Word) : Word :=
  acc + selectedTarget epoch validator flags

set_option maxHeartbeats 4000000 in
theorem targetFold_spec (epochReg flagsReg accReg : Reg)
    (base ptr flagsPtr epoch acc flagWord t5 t6 t7 : Word) (validator : Validator)
    (hacc : accReg ≠ .x0) :
    cpsTripleWithin (targetFold epochReg flagsReg accReg).length base (base + 72)
      (CodeReq.ofProg base (targetFold epochReg flagsReg accReg))
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (epochReg ↦ᵣ epoch) ** (flagsReg ↦ᵣ flagsPtr) **
        (accReg ↦ᵣ acc) ** (.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7) **
        validator.owns ptr ** ((flagsPtr + signExtend12 0) ↦ₘ flagWord))
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (epochReg ↦ᵣ epoch) ** (flagsReg ↦ᵣ flagsPtr) **
        (accReg ↦ᵣ foldedTarget acc epoch validator flagWord) **
        (.x5 ↦ᵣ targetBit epoch validator flagWord) **
        (.x6 ↦ᵣ selectedTarget epoch validator flagWord) **
        (.x7 ↦ᵣ targetMask epoch validator flagWord) **
        validator.owns ptr ** ((flagsPtr + signExtend12 0) ↦ₘ flagWord)) := by
  unfold targetFold foldedTarget selectedTarget targetMask targetBit flagBit unslashedWord
    slashedBit activeBit beforeExit notBeforeActivation Validator.owns
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  let actv := validator.activationEpoch
  let exitv := validator.exitEpoch
  let slashed := validator.slashed
  let eff := validator.effectiveBalance
  have s0 := ld_spec_gen_within .x5 .x10 ptr t5 actv 8 base (by decide)
  have s1 := ld_spec_gen_within .x6 .x10 ptr t6 exitv 16 (base + 4) (by decide)
  have s2 := sltu_spec_gen_within .x7 epochReg .x5 t7 epoch actv (base + 8) (by decide)
  have s3 := xori_spec_gen_same_within .x7
    (if BitVec.ult epoch actv then 1 else 0) 1 (base + 12) (by decide)
  have s4 := sltu_spec_gen_within .x5 epochReg .x6 actv epoch exitv (base + 16) (by decide)
  have s5 := and_spec_gen_rd_eq_rs1_within .x5 .x7
    (if BitVec.ult epoch exitv then 1 else 0)
    ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1) (base + 20) (by decide)
  have s6 := ld_spec_gen_within .x6 .x10 ptr exitv slashed 24 (base + 24) (by decide)
  have s7 := sltu_spec_gen_rd_eq_rs2_within .x6 .x0 0 slashed (base + 28) (by decide)
  have s8 := xori_spec_gen_same_within .x6
    (if BitVec.ult (0 : Word) slashed then 1 else 0) 1 (base + 32) (by decide)
  have s9 := and_spec_gen_rd_eq_rs1_within .x5 .x6
    ((if BitVec.ult epoch exitv then 1 else 0) &&&
      ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1))
    ((if BitVec.ult (0 : Word) slashed then 1 else 0) ^^^ signExtend12 1) (base + 36) (by decide)
  have s10 := ld_spec_gen_within .x6 flagsReg flagsPtr
    ((if BitVec.ult (0 : Word) slashed then 1 else 0) ^^^ signExtend12 1) flagWord 0
    (base + 40) (by decide)
  have s11 := andi_spec_gen_same_within .x6 flagWord 2 (base + 44) (by decide)
  have s12 := sltu_spec_gen_rd_eq_rs2_within .x6 .x0 0
    (flagWord &&& signExtend12 2) (base + 48) (by decide)
  have s13 := and_spec_gen_rd_eq_rs1_within .x5 .x6
    (((if BitVec.ult epoch exitv then 1 else 0) &&&
        ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1)) &&&
      ((if BitVec.ult (0 : Word) slashed then 1 else 0) ^^^ signExtend12 1))
    (if BitVec.ult (0 : Word) (flagWord &&& signExtend12 2) then 1 else 0) (base + 52) (by decide)
  have s14 := ld_spec_gen_within .x6 .x10 ptr
    (if BitVec.ult (0 : Word) (flagWord &&& signExtend12 2) then 1 else 0) eff 0
    (base + 56) (by decide)
  have s15 := sub_spec_gen_within .x7 .x0 .x5 0
    ((((if BitVec.ult epoch exitv then 1 else 0) &&&
          ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1)) &&&
        ((if BitVec.ult (0 : Word) slashed then 1 else 0) ^^^ signExtend12 1)) &&&
      (if BitVec.ult (0 : Word) (flagWord &&& signExtend12 2) then 1 else 0))
    ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1) (base + 60) (by decide)
  have s16 := and_spec_gen_rd_eq_rs1_within .x6 .x7 eff
    ((0 : Word) -
      ((((if BitVec.ult epoch exitv then 1 else 0) &&&
            ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1)) &&&
          ((if BitVec.ult (0 : Word) slashed then 1 else 0) ^^^ signExtend12 1)) &&&
        (if BitVec.ult (0 : Word) (flagWord &&& signExtend12 2) then 1 else 0)))
    (base + 64) (by decide)
  have s17 := add_spec_gen_rd_eq_rs1_within accReg .x6 acc
    (eff &&& ((0 : Word) -
      ((((if BitVec.ult epoch exitv then 1 else 0) &&&
            ((if BitVec.ult epoch actv then 1 else 0) ^^^ signExtend12 1)) &&&
          ((if BitVec.ult (0 : Word) slashed then 1 else 0) ^^^ signExtend12 1)) &&&
        (if BitVec.ult (0 : Word) (flagWord &&& signExtend12 2) then 1 else 0))))
    (base + 68) hacc
  runBlock s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17

theorem walk_spec (base ptr prev curr counter : Word) :
    cpsTripleWithin walk.length base (base + 16) (CodeReq.ofProg base walk)
      ((.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ prev) ** (.x12 ↦ᵣ curr) ** (.x13 ↦ᵣ counter))
      ((.x10 ↦ᵣ ptr + signExtend12 32) ** (.x11 ↦ᵣ prev + signExtend12 8) **
        (.x12 ↦ᵣ curr + signExtend12 8) ** (.x13 ↦ᵣ counter + signExtend12 4095)) := by
  unfold walk
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have s0 := addi_spec_gen_same_within .x10 ptr 32 base (by decide)
  have s1 := addi_spec_gen_same_within .x11 prev 8 (base + 4) (by decide)
  have s2 := addi_spec_gen_same_within .x12 curr 8 (base + 8) (by decide)
  have s3 := addi_spec_gen_same_within .x13 counter 4095 (base + 12) (by decide)
  runBlock s0 s1 s2 s3

theorem bitWord_if (b : Bool) : (if b then (1 : Word) else 0) = bitWord b := by
  cases b <;> rfl

theorem activeBit_spec (epoch : Word) (validator : Validator) :
    activeBit epoch validator.activationEpoch validator.exitEpoch =
      bitWord (isActiveValidator validator epoch) := by
  unfold activeBit notBeforeActivation beforeExit isActiveValidator bitWord
  cases BitVec.ult epoch validator.activationEpoch <;>
    cases BitVec.ult epoch validator.exitEpoch <;>
    simp only [Bool.not_true, Bool.not_false, oneSign] <;> bv_decide

theorem maskOfBit (bit : Word) (hb : bit = 0 ∨ bit = 1) :
    ((0 : Word) - bit) = if bit = 1 then BitVec.allOnes 64 else 0 := by
  rcases hb with rfl | rfl
  · rw [subZero]
    rfl
  · rw [subOnes, allOnesLit]
    simp

theorem selectByBit (eff bit : Word) (hb : bit = 0 ∨ bit = 1) :
    eff &&& ((0 : Word) - bit) = if bit = 1 then eff else 0 := by
  rw [maskOfBit bit hb]
  rcases hb with rfl | rfl <;> simp [andAllOnesLit]

theorem bitWord_zero_one (b : Bool) : bitWord b = 0 ∨ bitWord b = 1 := by
  cases b <;> simp [bitWord]

theorem selectedEffective_spec (epoch : Word) (validator : Validator) :
    selectedEffective epoch validator =
      if isActiveValidator validator epoch then validator.effectiveBalance else 0 := by
  unfold selectedEffective activeMask
  rw [activeBit_spec, selectByBit _ _ (bitWord_zero_one _)]
  cases isActiveValidator validator epoch <;> simp [bitWord]

theorem foldedActive_spec (acc epoch : Word) (validator : Validator)
    (_hbound : acc.toNat + contributionActive validator epoch < 2^64) :
    foldedActive acc epoch validator =
      BitVec.ofNat 64 (acc.toNat + contributionActive validator epoch) := by
  unfold foldedActive contributionActive contributesActive
  rw [selectedEffective_spec]
  cases h : isActiveValidator validator epoch
  · simp only [if_neg (by decide : ¬(false = true)), Nat.add_zero]
    exact (BitVec.add_zero (x := acc)).trans (wordNat acc)
  · exact wordAddWord acc validator.effectiveBalance

theorem ult_zero_bne (x : Word) : BitVec.ult (0 : Word) x = (x != 0) := by
  by_cases h : x = 0
  · subst h
    decide
  · have hlt : BitVec.ult (0 : Word) x = true := by
      rw [BitVec.ult_iff_toNat_lt]
      exact Nat.pos_of_ne_zero (fun hz => h (BitVec.eq_of_toNat_eq (by simpa using hz)))
    have hne : (x != 0) = true := by
      simpa [bne_iff_ne] using h
    rw [hlt, hne]

theorem unslashedWord_spec (validator : Validator)
    (hs : validator.slashed = 0 ∨ validator.slashed = 1) :
    unslashedWord validator.slashed = bitWord (isUnslashed validator) := by
  rcases hs with h | h <;> simp [unslashedWord, slashedBit, isUnslashed, h] <;> decide

theorem flagBit_spec (flags : Word) : flagBit flags = bitWord (hasTargetFlag flags) := by
  unfold flagBit hasTargetFlag
  rw [signTwo, ult_zero_bne]
  cases flags &&& 2 != 0 <;> simp [bitWord]

theorem targetBit_spec (epoch : Word) (validator : Validator) (flags : Word)
    (hs : validator.slashed = 0 ∨ validator.slashed = 1) :
    targetBit epoch validator flags =
      bitWord (contributesTarget validator flags epoch) := by
  unfold targetBit contributesTarget
  rw [activeBit_spec, unslashedWord_spec validator hs, flagBit_spec]
  exact and01 _ _ _ _ (and01 _ _ _ _ rfl rfl) rfl

theorem selectedTarget_spec (epoch : Word) (validator : Validator) (flags : Word)
    (hs : validator.slashed = 0 ∨ validator.slashed = 1) :
    selectedTarget epoch validator flags =
      if contributesTarget validator flags epoch then validator.effectiveBalance else 0 := by
  unfold selectedTarget targetMask
  rw [targetBit_spec _ _ _ hs, selectByBit _ _ (bitWord_zero_one _)]
  cases contributesTarget validator flags epoch <;> simp [bitWord]

theorem foldedTarget_spec (acc epoch : Word) (validator : Validator) (flags : Word)
    (hs : validator.slashed = 0 ∨ validator.slashed = 1)
    (_hbound : acc.toNat + contributionTarget validator flags epoch < 2^64) :
    foldedTarget acc epoch validator flags =
      BitVec.ofNat 64 (acc.toNat + contributionTarget validator flags epoch) := by
  unfold foldedTarget contributionTarget
  rw [selectedTarget_spec _ _ _ hs]
  cases h : contributesTarget validator flags epoch
  · simp only [if_neg (by decide : ¬(false = true)), Nat.add_zero]
    exact (BitVec.add_zero (x := acc)).trans (wordNat acc)
  · exact wordAddWord acc validator.effectiveBalance

theorem active_prev_disjoint (base : Word) :
    CodeReq.Disjoint (CodeReq.ofProg base (activeFold .x16 .x17))
      (CodeReq.ofProg (base + 40) (targetFold .x31 .x11 .x29)) := by
  apply CodeReq.ofProg_disjoint_range_len _ _ 10 _ _ 18 (by decide) (by decide)
  intro k1 k2 hk1 hk2
  bv_omega

theorem active_then_previous (base ptr prevPtr currPtr counter epoch previous total prevAcc currAcc
    t5 t6 t7 prevFlag currFlag : Word) (validator : Validator) :
    cpsTripleWithin ((activeFold .x16 .x17).length + (targetFold .x31 .x11 .x29).length)
      base (base + 40 + 72)
      ((CodeReq.ofProg base (activeFold .x16 .x17)).union
        (CodeReq.ofProg (base + 40) (targetFold .x31 .x11 .x29)))
      ((((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ total) **
          (.x5 ↦ᵣ t5) ** (.x6 ↦ᵣ t6) ** (.x7 ↦ᵣ t7) ** validator.owns ptr) **
        ((.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter) **
          (.x31 ↦ᵣ previous) ** (.x29 ↦ᵣ prevAcc) ** (.x30 ↦ᵣ currAcc) **
          ((prevPtr + signExtend12 0) ↦ₘ prevFlag) ** ((currPtr + signExtend12 0) ↦ₘ currFlag))))
      (((( .x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x31 ↦ᵣ previous) ** (.x11 ↦ᵣ prevPtr) **
        (.x29 ↦ᵣ foldedTarget prevAcc previous validator prevFlag) **
        (.x5 ↦ᵣ targetBit previous validator prevFlag) **
        (.x6 ↦ᵣ selectedTarget previous validator prevFlag) **
        (.x7 ↦ᵣ targetMask previous validator prevFlag) ** validator.owns ptr **
        ((prevPtr + signExtend12 0) ↦ₘ prevFlag)) **
        ((.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ foldedActive total epoch validator) **
          (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter) ** (.x30 ↦ᵣ currAcc) **
          ((currPtr + signExtend12 0) ↦ₘ currFlag)))) := by
  let frame : Assertion :=
    (.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter) **
      (.x31 ↦ᵣ previous) ** (.x29 ↦ᵣ prevAcc) ** (.x30 ↦ᵣ currAcc) **
      ((prevPtr + signExtend12 0) ↦ₘ prevFlag) ** ((currPtr + signExtend12 0) ↦ₘ currFlag)
  have hframe : frame.pcFree := by unfold frame; pcFree
  have active := cpsTripleWithin_frameR frame hframe
    (activeFold_x16_spec base ptr epoch total t5 t6 t7 validator)
  have previousFold := targetFold_spec .x31 .x11 .x29 (base + 40) ptr prevPtr previous prevAcc prevFlag
    (activeBit epoch validator.activationEpoch validator.exitEpoch)
    (selectedEffective epoch validator)
    (activeMask epoch validator.activationEpoch validator.exitEpoch) validator (by decide)
  have hjoin :
      (((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) **
        (.x17 ↦ᵣ foldedActive total epoch validator) **
        (.x5 ↦ᵣ activeBit epoch validator.activationEpoch validator.exitEpoch) **
        (.x6 ↦ᵣ selectedEffective epoch validator) **
        (.x7 ↦ᵣ activeMask epoch validator.activationEpoch validator.exitEpoch) **
        validator.owns ptr) ** frame) =
      (((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x31 ↦ᵣ previous) ** (.x11 ↦ᵣ prevPtr) **
        (.x29 ↦ᵣ prevAcc) **
        (.x5 ↦ᵣ activeBit epoch validator.activationEpoch validator.exitEpoch) **
        (.x6 ↦ᵣ selectedEffective epoch validator) **
        (.x7 ↦ᵣ activeMask epoch validator.activationEpoch validator.exitEpoch) **
        validator.owns ptr ** ((prevPtr + signExtend12 0) ↦ₘ prevFlag)) **
        ((.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ foldedActive total epoch validator) **
          (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter) ** (.x30 ↦ᵣ currAcc) **
          ((currPtr + signExtend12 0) ↦ₘ currFlag))) := by
    unfold frame
    xperm
  rw [hjoin] at active
  exact cpsTripleWithin_seq (active_prev_disjoint base) active
    (cpsTripleWithin_frameR
      ((.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ foldedActive total epoch validator) **
        (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter) ** (.x30 ↦ᵣ currAcc) **
        ((currPtr + signExtend12 0) ↦ₘ currFlag)) (by pcFree) previousFold)

theorem prefix_current_disjoint (base : Word) :
    CodeReq.Disjoint
      ((CodeReq.ofProg base (activeFold .x16 .x17)).union
        (CodeReq.ofProg (base + 40) (targetFold .x31 .x11 .x29)))
      (CodeReq.ofProg (base + 112) (targetFold .x16 .x12 .x30)) := by
  refine CodeReq.Disjoint.union_left ?_ ?_
  · apply CodeReq.ofProg_disjoint_range_len _ _ 10 _ _ 18 (by decide) (by decide)
    intro k1 k2 hk1 hk2
    bv_omega
  · apply CodeReq.ofProg_disjoint_range_len _ _ 18 _ _ 18 (by decide) (by decide)
    intro k1 k2 hk1 hk2
    bv_omega

theorem body_walk_disjoint (base : Word) :
    CodeReq.Disjoint
      (((CodeReq.ofProg base (activeFold .x16 .x17)).union
          (CodeReq.ofProg (base + 40) (targetFold .x31 .x11 .x29))).union
        (CodeReq.ofProg (base + 112) (targetFold .x16 .x12 .x30)))
      (CodeReq.ofProg (base + 184) walk) := by
  refine CodeReq.Disjoint.union_left (CodeReq.Disjoint.union_left ?_ ?_) ?_
  · apply CodeReq.ofProg_disjoint_range_len _ _ 10 _ _ 4 (by decide) (by decide)
    intro k1 k2 hk1 hk2
    bv_omega
  · apply CodeReq.ofProg_disjoint_range_len _ _ 18 _ _ 4 (by decide) (by decide)
    intro k1 k2 hk1 hk2
    bv_omega
  · apply CodeReq.ofProg_disjoint_range_len _ _ 18 _ _ 4 (by decide) (by decide)
    intro k1 k2 hk1 hk2
    bv_omega

theorem bodyStraight_code (base : Word) :
    ((((CodeReq.ofProg base (activeFold .x16 .x17)).union
          (CodeReq.ofProg (base + 40) (targetFold .x31 .x11 .x29))).union
        (CodeReq.ofProg (base + 112) (targetFold .x16 .x12 .x30))).union
      (CodeReq.ofProg (base + 184) walk)) =
      CodeReq.ofProg base bodyStraight := by
  unfold bodyStraight
  rw [CodeReq.ofProg_append, CodeReq.ofProg_append, CodeReq.ofProg_append]
  simp only [show (activeFold .x16 .x17).length = 10 from rfl, CodeReq.union_assoc]
  rfl

theorem bodyStraight_spec (base ptr prevPtr currPtr counter epoch previous total prevAcc currAcc
    t5 t6 t7 prevFlag currFlag : Word) (validator : Validator) :
    cpsTripleWithin ((activeFold .x16 .x17).length + (targetFold .x31 .x11 .x29).length +
        (targetFold .x16 .x12 .x30).length + walk.length) base (base + 184 + 16)
      ((((CodeReq.ofProg base (activeFold .x16 .x17)).union
            (CodeReq.ofProg (base + 40) (targetFold .x31 .x11 .x29))).union
          (CodeReq.ofProg (base + 112) (targetFold .x16 .x12 .x30))).union
        (CodeReq.ofProg (base + 184) walk))
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
  have prefixSpec := active_then_previous base ptr prevPtr currPtr counter epoch previous total
    prevAcc currAcc t5 t6 t7 prevFlag currFlag validator
  have hmid : base + 40 + 72 = base + 112 := by bv_omega
  rw [hmid] at prefixSpec
  let rest : Assertion :=
    (.x31 ↦ᵣ previous) ** (.x11 ↦ᵣ prevPtr) **
      (.x29 ↦ᵣ foldedTarget prevAcc previous validator prevFlag) **
      ((prevPtr + signExtend12 0) ↦ₘ prevFlag) **
      (.x17 ↦ᵣ foldedActive total epoch validator) ** (.x13 ↦ᵣ counter)
  have hjoin :
      (((( .x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x31 ↦ᵣ previous) ** (.x11 ↦ᵣ prevPtr) **
          (.x29 ↦ᵣ foldedTarget prevAcc previous validator prevFlag) **
          (.x5 ↦ᵣ targetBit previous validator prevFlag) **
          (.x6 ↦ᵣ selectedTarget previous validator prevFlag) **
          (.x7 ↦ᵣ targetMask previous validator prevFlag) ** validator.owns ptr **
          ((prevPtr + signExtend12 0) ↦ₘ prevFlag)) **
        ((.x16 ↦ᵣ epoch) ** (.x17 ↦ᵣ foldedActive total epoch validator) **
          (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter) ** (.x30 ↦ᵣ currAcc) **
          ((currPtr + signExtend12 0) ↦ₘ currFlag))) =
      ((((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) ** (.x12 ↦ᵣ currPtr) **
          (.x30 ↦ᵣ currAcc) ** (.x5 ↦ᵣ targetBit previous validator prevFlag) **
          (.x6 ↦ᵣ selectedTarget previous validator prevFlag) **
          (.x7 ↦ᵣ targetMask previous validator prevFlag) ** validator.owns ptr **
          ((currPtr + signExtend12 0) ↦ₘ currFlag)) ** rest))) := by
    unfold rest
    xperm
  rw [hjoin] at prefixSpec
  have current := cpsTripleWithin_frameR rest (by unfold rest; pcFree)
    (targetFold_spec .x16 .x12 .x30 (base + 112) ptr currPtr epoch currAcc currFlag
      (targetBit previous validator prevFlag) (selectedTarget previous validator prevFlag)
      (targetMask previous validator prevFlag) validator (by decide))
  have folded := cpsTripleWithin_seq (prefix_current_disjoint base) prefixSpec current
  have hwalk : base + 112 + 72 = base + 184 := by bv_omega
  rw [hwalk] at folded
  let kept : Assertion :=
    (((.x0 ↦ᵣ 0) ** (.x16 ↦ᵣ epoch) **
        (.x30 ↦ᵣ foldedTarget currAcc epoch validator currFlag) **
        (.x5 ↦ᵣ targetBit epoch validator currFlag) **
        (.x6 ↦ᵣ selectedTarget epoch validator currFlag) **
        (.x7 ↦ᵣ targetMask epoch validator currFlag) ** validator.owns ptr **
        ((currPtr + signExtend12 0) ↦ₘ currFlag)) **
      ((.x31 ↦ᵣ previous) **
        (.x29 ↦ᵣ foldedTarget prevAcc previous validator prevFlag) **
        ((prevPtr + signExtend12 0) ↦ₘ prevFlag) **
        (.x17 ↦ᵣ foldedActive total epoch validator)))
  have hwalkJoin :
      (((( .x0 ↦ᵣ 0) ** (.x10 ↦ᵣ ptr) ** (.x16 ↦ᵣ epoch) ** (.x12 ↦ᵣ currPtr) **
          (.x30 ↦ᵣ foldedTarget currAcc epoch validator currFlag) **
          (.x5 ↦ᵣ targetBit epoch validator currFlag) **
          (.x6 ↦ᵣ selectedTarget epoch validator currFlag) **
          (.x7 ↦ᵣ targetMask epoch validator currFlag) ** validator.owns ptr **
          ((currPtr + signExtend12 0) ↦ₘ currFlag)) ** rest) =
      ((((.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ prevPtr) ** (.x12 ↦ᵣ currPtr) ** (.x13 ↦ᵣ counter)) **
        kept))) := by
    unfold rest kept
    xperm
  rw [hwalkJoin] at folded
  have hkept : kept.pcFree := by unfold kept; pcFree
  exact cpsTripleWithin_seq (body_walk_disjoint base) folded
    (cpsTripleWithin_frameR kept hkept (walk_spec (base + 184) ptr prevPtr currPtr counter))

end ClAsm.Aggregate
