import ClAsm.Arithmetic

namespace ClAsm.Arithmetic

open RiscvZkvm.Rv64

theorem previousValue_toNat (epoch : Word) :
    (previousValue epoch).toNat = epoch.toNat - 1 := by
  by_cases h : epoch.toNat = 0
  · have he : epoch = 0 := BitVec.eq_of_toNat_eq h
    subst he; decide
  · have hult : ¬ epoch.toNat < 1 := by omega
    have hvalue : previousValue epoch = epoch - 1 := by
      simp [previousValue, BitVec.ult, hult, signExtend12, BitVec.sub_eq_add_neg]
    rw [hvalue, BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
    rfl

theorem shiftedBits_toNat (bits : Word) :
    (shiftedBits bits).toNat = (bits.toNat * 2) % 16 := by
  simp [shiftedBits, BitVec.toNat_and, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [show (15 : Nat) = 2^4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2^64)

theorem thresholdValue_correct (vote total : Word)
    (hv : 3 * vote.toNat < 2^64) (ht : 2 * total.toNat < 2^64) :
    thresholdValue vote total = if 3 * vote.toNat ≥ 2 * total.toNat then 1 else 0 := by
  have hv2 : (vote <<< (1 : Nat)).toNat = 2 * vote.toNat := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hv3 : ((vote <<< (1 : Nat)) + vote).toNat = 3 * vote.toNat := by
    rw [BitVec.toNat_add, hv2, Nat.mod_eq_of_lt (by omega)]; omega
  have ht2 : (total <<< (1 : Nat)).toNat = 2 * total.toNat := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  unfold thresholdValue
  simp only [BitVec.ult, hv3, ht2]
  split <;> simp_all <;> omega

theorem rootOffset_toNat (epoch : Word) :
    (rootOffset epoch).toNat = ((epoch.toNat * 32) % 8192) * 32 := by
  simp [rootOffset, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq]
  rw [show (255 : Nat) = 2^8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hbound : epoch.toNat % 256 * 1024 < 2^64 := by
    have := Nat.mod_lt epoch.toNat (by decide : 0 < 256)
    omega
  rw [Nat.mod_eq_of_lt hbound]
  have hindex := Nat.mul_mod_mul_right 32 epoch.toNat 256
  simp only [show 256 * 32 = 8192 from rfl] at hindex
  rw [hindex]
  omega

theorem rootOffset_in_bounds (epoch : Word) :
    (rootOffset epoch).toNat + Layout.rootBytes ≤ Layout.rootsBytes := by
  rw [rootOffset_toNat]
  have := Nat.mod_lt (epoch.toNat * 32) (by decide : 0 < 8192)
  simp only [Layout.rootBytes, Layout.rootsBytes, Layout.slotsPerHistoricalRoot]
  omega

theorem rootOffset_aligned (epoch : Word) : (rootOffset epoch).toNat % 8 = 0 := by
  rw [rootOffset_toNat]
  omega

end ClAsm.Arithmetic
