import ClAsm.Probes
import ClAsm.Arithmetic.Proof
import ClAsm.Checkpoint.Proof
import ClAsm.EpochAtSlot.Proof
import RiscvZkvm.Rv64.Logic.BitAux
import RiscvZkvm.Rv64.Logic.ControlFlow

namespace ClAsm.Probes

open RiscvZkvm.Rv64

private theorem return_spec (base ret : Word) (hret : ret &&& 1 = 0) :
    cpsTripleWithin 1 base ret (CodeReq.singleton base (.JALR .x0 .x1 0))
      (.x1 ↦ᵣ ret) (.x1 ↦ᵣ ret) := by
  have jump := jalr_x0_spec_gen_within .x1 ret 0 base
  have target : (ret + signExtend12 0) &&& ~~~(1 : Word) = ret := by
    simpa [signExtend12] using BitAux.word_andn_one_of_even hret
  rw [target] at jump
  exact jump

theorem epochAtSlot_spec (base ptr slot old ret : Word) (hret : ret &&& 1 = 0) :
    cpsTripleWithin Kind.epochAtSlot.program.length base ret
      (CodeReq.ofProg base Kind.epochAtSlot.program)
      (EpochAtSlot.pre ptr slot old ret) (EpochAtSlot.post ptr slot ret) :=
  EpochAtSlot.callable_spec base ptr slot old ret hret

theorem previousEpoch_spec (base epoch old ret : Word) (hret : ret &&& 1 = 0) :
    cpsTripleWithin Kind.previousEpoch.program.length base ret
      (CodeReq.ofProg base Kind.previousEpoch.program)
      ((.x10 ↦ᵣ epoch) ** (.x5 ↦ᵣ old) ** (.x1 ↦ᵣ ret))
      ((.x10 ↦ᵣ epoch) ** (.x5 ↦ᵣ Arithmetic.previousValue epoch) ** (.x1 ↦ᵣ ret)) := by
  unfold Kind.program Kind.body Arithmetic.previousEpoch
  simp only [List.cons_append, List.nil_append, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have body := Arithmetic.previousEpoch_spec .x10 .x5 base epoch old (by decide) (by decide)
  simp only [Arithmetic.previousEpoch, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    List.length_cons, List.length_nil] at body
  have jump := return_spec (base + 12) ret hret
  runBlock body jump

theorem shiftBits_spec (base bits ret : Word) (hret : ret &&& 1 = 0) :
    cpsTripleWithin Kind.shiftBits.program.length base ret
      (CodeReq.ofProg base Kind.shiftBits.program)
      ((.x5 ↦ᵣ bits) ** (.x1 ↦ᵣ ret))
      ((.x5 ↦ᵣ Arithmetic.shiftedBits bits) ** (.x1 ↦ᵣ ret)) := by
  unfold Kind.program Kind.body Arithmetic.shiftJustificationBits
  simp only [List.cons_append, List.nil_append, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have body := Arithmetic.shiftJustificationBits_spec .x5 base bits (by decide)
  simp only [Arithmetic.shiftJustificationBits, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    List.length_cons, List.length_nil] at body
  have jump := return_spec (base + 8) ret hret
  runBlock body jump

theorem supermajority_spec (base vote total oldTriple oldTwice ret : Word)
    (hret : ret &&& 1 = 0) :
    cpsTripleWithin Kind.supermajority.program.length base ret
      (CodeReq.ofProg base Kind.supermajority.program)
      ((.x10 ↦ᵣ vote) ** (.x11 ↦ᵣ total) ** (.x5 ↦ᵣ oldTriple) **
        (.x6 ↦ᵣ oldTwice) ** (.x1 ↦ᵣ ret))
      ((.x10 ↦ᵣ vote) ** (.x11 ↦ᵣ total) ** (.x5 ↦ᵣ Arithmetic.thresholdValue vote total) **
        (.x6 ↦ᵣ total <<< (1 : Nat)) ** (.x1 ↦ᵣ ret)) := by
  unfold Kind.program Kind.body Arithmetic.hasSupermajority
  simp only [List.cons_append, List.nil_append, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have body := Arithmetic.hasSupermajority_spec .x10 .x11 .x5 .x6
    base vote total oldTriple oldTwice (by decide) (by decide) (by decide)
  simp only [Arithmetic.hasSupermajority, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    List.length_cons, List.length_nil] at body
  have jump := return_spec (base + 20) ret hret
  runBlock body jump

theorem rootAddress_spec (base epoch roots old ret : Word) (hret : ret &&& 1 = 0) :
    cpsTripleWithin Kind.rootAddress.program.length base ret
      (CodeReq.ofProg base Kind.rootAddress.program)
      ((.x10 ↦ᵣ epoch) ** (.x11 ↦ᵣ roots) ** (.x5 ↦ᵣ old) ** (.x1 ↦ᵣ ret))
      ((.x10 ↦ᵣ epoch) ** (.x11 ↦ᵣ roots) **
        (.x5 ↦ᵣ roots + Arithmetic.rootOffset epoch) ** (.x1 ↦ᵣ ret)) := by
  unfold Kind.program Kind.body Arithmetic.blockRootAddress
  simp only [List.cons_append, List.nil_append, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have body := Arithmetic.blockRootAddress_spec .x10 .x11 .x5
    base epoch roots old (by decide) (by decide)
  simp only [Arithmetic.blockRootAddress, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    List.length_cons, List.length_nil] at body
  have jump := return_spec (base + 12) ret hret
  runBlock body jump

theorem checkpointCopy_spec (base source target oldTmp ret : Word) (value old : Checkpoint)
    (hret : ret &&& 1 = 0) :
    cpsTripleWithin Kind.checkpointCopy.program.length base ret
      (CodeReq.ofProg base Kind.checkpointCopy.program)
      ((.x10 ↦ᵣ source) ** (.x11 ↦ᵣ target) ** (.x5 ↦ᵣ oldTmp) **
        value.owns source ** old.owns target ** (.x1 ↦ᵣ ret))
      ((.x10 ↦ᵣ source) ** (.x11 ↦ᵣ target) ** (.x5 ↦ᵣ value.root.w3) **
        value.owns source ** value.owns target ** (.x1 ↦ᵣ ret)) := by
  unfold Kind.program Kind.body copyCheckpoint
  simp only [List.cons_append, List.nil_append, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have body := copyCheckpoint_spec .x10 .x11 .x5
    base source target oldTmp value old (by decide) (by decide)
  simp only [copyCheckpoint, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    List.length_cons, List.length_nil] at body
  have jump := return_spec (base + 40) ret hret
  runBlock body jump

theorem rootCopy_spec (base source target oldTmp ret : Word) (value old : Root)
    (hret : ret &&& 1 = 0) :
    cpsTripleWithin Kind.rootCopy.program.length base ret
      (CodeReq.ofProg base Kind.rootCopy.program)
      ((.x10 ↦ᵣ source) ** (.x11 ↦ᵣ target) ** (.x5 ↦ᵣ oldTmp) **
        value.owns source ** old.owns target ** (.x1 ↦ᵣ ret))
      ((.x10 ↦ᵣ source) ** (.x11 ↦ᵣ target) ** (.x5 ↦ᵣ value.w3) **
        value.owns source ** value.owns target ** (.x1 ↦ᵣ ret)) := by
  unfold Kind.program Kind.body copyRoot
  simp only [List.cons_append, List.nil_append, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have body := copyRoot_spec .x10 .x11 .x5
    base source target oldTmp value old (by decide) (by decide)
  simp only [copyRoot, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    List.length_cons, List.length_nil] at body
  have jump := return_spec (base + 32) ret hret
  runBlock body jump

end ClAsm.Probes
