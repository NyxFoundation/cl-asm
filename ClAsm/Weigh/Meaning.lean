import ClAsm.Weigh.Execution

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

@[simp] theorem finalizeRegisters_epoch (a : Addresses) (r : Registers) (saved : Checkpoint)
    (offset delta mask : BitVec 12) :
    (finalizeRegisters a r saved offset delta mask).prologue.epoch = r.prologue.epoch := by
  unfold finalizeRegisters
  dsimp only
  split <;> rfl

@[simp] theorem finalizeRegisters_bits (a : Addresses) (r : Registers) (saved : Checkpoint)
    (offset delta mask : BitVec 12) :
    (finalizeRegisters a r saved offset delta mask).prologue.bits = r.prologue.bits := by
  unfold finalizeRegisters
  dsimp only
  split <;> rfl

@[simp] theorem finalizationResult_bits (a : Addresses) (state : State) (r : Registers) :
    (finalizationResult a state r).1.prologue.bits = r.prologue.bits := by
  simp only [finalizationResult, finalizeRegisters_bits]

theorem finalizationCheckpoint_correct (r : Registers) (saved old : Checkpoint)
    (currentEpoch : Nat) (delta mask : BitVec 12)
    (hd : (signExtend12 delta).toNat = delta.toNat)
    (hm : (signExtend12 mask).toNat = mask.toNat)
    (he : r.prologue.epoch.toNat = currentEpoch)
    (hadd : saved.epoch.toNat + delta.toNat < 2^64) :
    finalizationCheckpoint r saved old delta mask =
      if finalizationHolds r.prologue.bits saved currentEpoch delta.toNat mask.toNat then saved else old := by
  unfold finalizationCheckpoint
  rw [finalizationValue_correct _ _ _ _ _ hd hm hadd, he]
  by_cases h : r.prologue.bits.toNat &&& mask.toNat = mask.toNat ∧
      saved.epoch.toNat + delta.toNat = currentEpoch
  · simp [h, finalizationHolds]
  · by_cases hm' : r.prologue.bits.toNat &&& mask.toNat = mask.toNat <;>
      simp_all [finalizationHolds]

theorem finalizationResult_correct (a : Addresses) (state : State) (r : Registers)
    (he : r.prologue.epoch.toNat = epoch state)
    (hp : state.previous.epoch.toNat + 3 < 2^64)
    (hc : state.current.epoch.toNat + 2 < 2^64) :
    (finalizationResult a state r).2 = finalizedCheckpoint state r.prologue.bits := by
  dsimp only [finalizationResult]
  rw [finalizationCheckpoint_correct _ _ _ (epoch state) 1 3 (by decide) (by decide)
      (by simpa using he) (by simp; omega)]
  rw [finalizationCheckpoint_correct _ _ _ (epoch state) 2 7 (by decide) (by decide)
      (by simpa using he) (by simpa using hc)]
  rw [finalizationCheckpoint_correct _ _ _ (epoch state) 2 6 (by decide) (by decide)
      (by simpa using he) (by simp; omega)]
  rw [finalizationCheckpoint_correct _ _ _ (epoch state) 3 14 (by decide) (by decide)
      he (by simpa using hp)]
  simp [finalizedCheckpoint]

theorem justificationValue_correct (balances : Balances) (current : Bool)
    (hv : 3 * (justificationVote balances current).toNat < 2^64)
    (ht : 2 * balances.total.toNat < 2^64) :
    justificationValue balances current =
      if threshold (justificationVote balances current) balances.total then 1 else 0 := by
  simp [justificationValue, Arithmetic.thresholdValue_correct _ _ hv ht, threshold]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem justificationResult_correct (a : Addresses) (state : State) (balances : Balances)
    (r : Registers) (roots : RootArray) (valid : ValidInput state balances) :
    (justificationResult a state balances r roots).1.prologue.epoch.toNat = epoch state ∧
    (justificationResult a state balances r roots).1.prologue.bits =
      (transition state balances roots.at).bits ∧
    (justificationResult a state balances r roots).2 = (transition state balances roots.at).current := by
  have he := EpochAtSlot.epoch_toNat state.slot
  have hp := Arithmetic.previousValue_toNat (EpochAtSlot.epoch state.slot)
  have hb := Arithmetic.shiftedBits_toNat state.bits
  have ew : EpochAtSlot.epoch state.slot = BitVec.ofNat 64 (epoch state) := by
    unfold epoch
    rw [← he]
    simp
  have heBound : state.slot.toNat / Layout.slotsPerEpoch < 2^64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) state.slot.isLt
  have hpBound : state.slot.toNat / Layout.slotsPerEpoch - 1 < 2^64 := by omega
  have pw : Arithmetic.previousValue (EpochAtSlot.epoch state.slot) =
      BitVec.ofNat 64 (previousEpoch state) := by
    unfold previousEpoch epoch
    rw [← he, ← hp]
    simp
  rw [ew] at pw
  simp only [epoch, previousEpoch] at ew pw
  have bw : Arithmetic.shiftedBits state.bits = BitVec.ofNat 64 ((state.bits.toNat * 2) % 16) := by
    rw [← hb]
    simp
  have vp := justificationValue_correct balances false valid.previousProduct valid.totalProduct
  have vc := justificationValue_correct balances true valid.currentProduct valid.totalProduct
  by_cases p : threshold balances.previous balances.total = true <;>
    by_cases c : threshold balances.current balances.total = true <;>
    simp [justificationVote] at vp vc <;>
    simp [justificationResult, justifyRegisters, justifiedCheckpoint, justificationEpoch,
      justificationBit, prologueRegisters, vp, vc, p, c, transition, bw,
      ← BitVec.ofNat_or, epoch, previousEpoch, ew, pw, signExtend12,
      Nat.mod_eq_of_lt heBound, Nat.mod_eq_of_lt hpBound]

theorem executionResult_correct (a : Addresses) (state : State) (balances : Balances)
    (r : Registers) (roots : RootArray) (valid : ValidInput state balances) :
    (executionResult a state balances r roots).2 = transition state balances roots.at := by
  obtain ⟨he, hb, hc⟩ := justificationResult_correct a state balances r roots valid
  have hf := finalizationResult_correct a state (justificationResult a state balances r roots).1
    he valid.previousAddition valid.currentAddition
  dsimp only [executionResult]
  simp only [finalizationResult_bits, hf, hb, hc]
  rfl

end ClAsm.Weigh
