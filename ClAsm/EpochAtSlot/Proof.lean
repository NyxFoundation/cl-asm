import ClAsm.EpochAtSlot
import RiscvZkvm.Rv64.Logic.SyscallSpecs
import RiscvZkvm.Rv64.Logic.ControlFlow
import RiscvZkvm.Rv64.Logic.BitAux
import RiscvZkvm.Rv64.Logic.AddrNorm
import RiscvZkvm.Rv64.Logic.Tactics.RunBlock

namespace ClAsm.EpochAtSlot

open RiscvZkvm.Rv64

/-- Two modeled steps, with ownership of the input cell and destination register.
    All other owned resources are preserved by the triple's built-in frame rule. -/
theorem program_spec (state dst : Reg) (base ptr slot oldDst : Word)
    (hdst : dst ≠ .x0) (_hne : state ≠ dst) :
    cpsTripleWithin (program state dst).length base (base + 8)
      (CodeReq.ofProg base (program state dst))
      ((state ↦ᵣ ptr) ** (dst ↦ᵣ oldDst) ** (ptr ↦ₘ slot))
      ((state ↦ᵣ ptr) ** (dst ↦ᵣ epoch slot) ** (ptr ↦ₘ slot)) := by
  unfold program epoch
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have loadSpec : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD dst state 0))
      ((state ↦ᵣ ptr) ** (dst ↦ᵣ oldDst) ** (ptr ↦ₘ slot))
      ((state ↦ᵣ ptr) ** (dst ↦ᵣ slot) ** (ptr ↦ₘ slot)) := by
    simpa [signExtend12] using ld_spec_within dst state ptr oldDst slot 0 base hdst
  have shiftSpec : cpsTripleWithin 1 (base + 4) (base + 4 + 4)
      (CodeReq.singleton (base + 4) (.SRLI dst dst 5))
      (dst ↦ᵣ slot) (dst ↦ᵣ (slot >>> (5 : Nat))) := by
    simpa using srli_spec_gen_same_within dst slot 5 (base + 4) hdst
  runBlock loadSpec shiftSpec

def pre (ptr slot oldDst ret : Word) : Assertion :=
  (.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ oldDst) ** (ptr ↦ₘ slot) ** (.x1 ↦ᵣ ret)

def post (ptr slot ret : Word) : Assertion :=
  (.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ epoch slot) ** (ptr ↦ₘ slot) ** (.x1 ↦ᵣ ret)

/-- The complete callable probe returns through ra within its instruction count. -/
theorem callable_spec (base ptr slot oldDst ret : Word) (hret : ret &&& 1 = 0) :
    cpsTripleWithin stepBound base ret (CodeReq.ofProg base callable)
      (pre ptr slot oldDst ret) (post ptr slot ret) := by
  unfold stepBound callable program pre post epoch
  simp only [List.cons_append, List.nil_append, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have loadSpec : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LD .x5 .x10 0))
      ((.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ oldDst) ** (ptr ↦ₘ slot))
      ((.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ slot) ** (ptr ↦ₘ slot)) := by
    simpa [signExtend12] using ld_spec_within .x5 .x10 ptr oldDst slot 0 base (by decide)
  have shiftSpec : cpsTripleWithin 1 (base + 4) (base + 4 + 4)
      (CodeReq.singleton (base + 4) (.SRLI .x5 .x5 5))
      (.x5 ↦ᵣ slot) (.x5 ↦ᵣ (slot >>> (5 : Nat))) := by
    simpa using srli_spec_gen_same_within .x5 slot 5 (base + 4) (by decide)
  have returnSpec : cpsTripleWithin 1 (base + 8) ret
      (CodeReq.singleton (base + 8) (.JALR .x0 .x1 0)) (.x1 ↦ᵣ ret) (.x1 ↦ᵣ ret) := by
    have jump := jalr_x0_spec_gen_within .x1 ret 0 (base + 8)
    have target : (ret + signExtend12 0) &&& ~~~(1 : Word) = ret := by
      simpa [signExtend12] using BitAux.word_andn_one_of_even hret
    rw [target] at jump
    exact jump
  runBlock loadSpec shiftSpec returnSpec

end ClAsm.EpochAtSlot
