import ClAsm.Aggregate.LoopProof
import ClAsm.Aggregate.Epilogue

namespace ClAsm.Aggregate

open RiscvZkvm.Rv64

def executionRegisters (input : Input) (r : Registers) : Registers :=
  let epoch := currentEpoch input
  let temps := lastTemps epoch (r.t5, r.t6, r.t7) input.validators input.currentFlags
  { t5 := floorBit (BitVec.ofNat 64 (sumTarget input.validators input.currentFlags epoch))
    t6 := temps.2.1
    t7 := temps.2.2
    epoch := epoch
    total := BitVec.ofNat 64 (sumActive input.validators epoch)
    increment := incrementWord
    previous := BitVec.ofNat 64
      (sumTarget input.validators input.previousFlags (previousEpochWord input))
    current := BitVec.ofNat 64 (sumTarget input.validators input.currentFlags epoch)
    previousEpoch := previousEpochWord input }

private theorem return_even (a : Addresses) (n : Nat) (ha : ValidAddresses a n) :
    a.returnAddress &&& 1 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change a.returnAddress.toNat &&& 1 = 0
  rw [show (1 : Nat) = 2^1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := ha.returnAligned
  omega

set_option maxHeartbeats 4000000 in
theorem program_spec (a : Addresses) (input : Input) (r : Registers)
    (oldT oldP oldC : Word) (ha : ValidAddresses a input.validators.length)
    (hi : ValidInput input) :
    cpsTripleWithin (stepBound input.validators.length) a.entry a.returnAddress
      (CodeReq.ofProg a.entry program) (precondition a input r oldT oldP oldC)
      (postcondition a input) := by
  haveI : Assertion.PCFree (validatorsOwn a.validators input.validators) :=
    ⟨validatorsOwn_pcFree _ _⟩
  haveI : Assertion.PCFree (wordsOwn a.previousFlags input.previousFlags) :=
    ⟨wordsOwn_pcFree _ _⟩
  haveI : Assertion.PCFree (wordsOwn a.currentFlags input.currentFlags) :=
    ⟨wordsOwn_pcFree _ _⟩
  have p := prologue_meaning a.entry input.slot r.epoch r.total r.increment r.previous
    r.current r.previousEpoch
  have l := loop_frame (a.entry + 36) a.validators a.previousFlags a.currentFlags
    a.returnAddress input.slot a.scratch incrementWord oldT oldP oldC
    (currentEpoch input) (previousEpochWord input) r.t5 r.t6 r.t7 [] [] []
    input.validators input.previousFlags input.currentFlags hi.previousLength hi.currentLength
    rfl rfl ha.validatorsNoWrap ha.previousFlagsNoWrap ha.currentFlagsNoWrap hi.slashed
    (by simpa using hi.active) (by simpa using hi.previous) (by simpa using hi.current)
    empAssertion pcFree_emp
  have e := epilogue_spec (a.entry + 248) a.scratch a.returnAddress
    (BitVec.ofNat 64 (sumActive input.validators (currentEpoch input)))
    (BitVec.ofNat 64 (sumTarget input.validators input.previousFlags (previousEpochWord input)))
    (BitVec.ofNat 64 (sumTarget input.validators input.currentFlags (currentEpoch input)))
    oldT oldP oldC
    (lastTemps (currentEpoch input) (r.t5, r.t6, r.t7) input.validators input.currentFlags).1 (return_even a _ ha)
  have hend : ((a.entry + 36) + 4) + signExtend21 loopExitOffset = a.entry + 248 := by
    rw [loopExit_word, bodyStraight_length]
    bv_omega
  rw [hend] at l
  have p := extendBlock (base := a.entry) (whole := program) 0 (by simp)
    (by decide) (by decide) (by decide) p
  have l := extendBlock (base := a.entry) (whole := program) 9 rfl
    (by decide) (by decide) (by decide) l
  have e := extendBlock (base := a.entry) (whole := program) 62 rfl
    (by decide) (by decide) (by decide) e
  rw [floorWord_spec _ hi.active, floorWord_spec _ hi.previous, floorWord_spec _ hi.current] at e
  have whole : cpsTripleWithin (stepBound input.validators.length) a.entry a.returnAddress
      (CodeReq.ofProg a.entry program) (precondition a input r oldT oldP oldC)
      ((executionRegisters input r).owns ** callRegisters a input input.validators.length **
        arraysOwn a input ** scratchOwn a (aggregateResult input).1 (aggregateResult input).2.1
          (aggregateResult input).2.2) := by
    generalize hcode : CodeReq.ofProg a.entry program = code at p l e ⊢
    simp only [guardCore, tailFrame, List.nil_append, validatorsOwn, wordsOwn,
      sumActive, sumTarget, sumTargetPairs, List.zip_nil_left,
      List.length_nil, sepConj_emp_left', sepConj_emp_right'] at l
    simp only [precondition, Registers.owns, callRegisters, arraysOwn, scratchOwn,
      executionRegisters, aggregateResult, finalPtr, Nat.mul_zero, Nat.sub_zero, Nat.sub_self,
      BitVec.add_zero] at l ⊢
    have hcount : stepBound input.validators.length = 9 + (2 + 52 * input.validators.length) + 13 := by
      unfold stepBound
      omega
    rw [hcount]
    simp only [currentEpoch, previousEpochWord, sumTarget, BitVec.ofNat_eq_ofNat] at p l e ⊢
    all_goals (runBlock p l e)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hp => ⟨executionRegisters input r, hp⟩) whole

end ClAsm.Aggregate
