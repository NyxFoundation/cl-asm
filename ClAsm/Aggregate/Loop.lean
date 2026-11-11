import ClAsm.Aggregate.Contract
import ClAsm.Arithmetic.Proof
import ClAsm.EpochAtSlot.Proof
import RiscvZkvm.Rv64.Logic.Tactics.RunBlock
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

end ClAsm.Aggregate
