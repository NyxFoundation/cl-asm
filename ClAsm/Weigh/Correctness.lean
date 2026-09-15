import ClAsm.Weigh.Proof
import ClAsm.Weigh.Meaning

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

/-- The complete emitted routine implements the reference-condition transition,
    returns within 175 steps, and preserves every disjoint caller-owned frame. -/
theorem program_spec (a : Addresses) (state : State) (balances : Balances) (r : Registers)
    (roots : RootArray) (scratch0 scratch1 : Checkpoint)
    (addresses : ValidAddresses a) (valid : ValidInput state balances) :
    cpsTripleWithin stepBound a.entry a.returnAddress (CodeReq.ofProg a.entry program)
      (precondition a state balances r roots scratch0 scratch1)
      (postcondition a state balances roots) := by
  have hret : a.returnAddress &&& 1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change a.returnAddress.toNat &&& 1 = 0
    rw [show (1 : Nat) = 2^1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have := addresses.returnAligned
    omega
  apply cpsTripleWithin_weaken (fun _ h => h) ?_
    (program_execution_spec a state balances r roots scratch0 scratch1 hret)
  intro heap hpost
  refine ⟨(executionResult a state balances r roots).1, ?_⟩
  rwa [executionResult_correct a state balances r roots valid] at hpost

end ClAsm.Weigh
