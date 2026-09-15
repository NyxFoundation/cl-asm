import ClAsm.Checkpoint
import RiscvZkvm.Rv64.Logic.SyscallSpecs
import RiscvZkvm.Rv64.Logic.Tactics.RunBlock
import RiscvZkvm.Rv64.Logic.AddrNorm

namespace ClAsm

open RiscvZkvm.Rv64

private theorem copyWord_spec (src dst tmp : Reg) (base source target oldTmp value old : Word)
    (offset : BitVec 12) (htmp : tmp ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.union (CodeReq.singleton base (.LD tmp src offset))
        (CodeReq.singleton (base + 4) (.SD dst tmp offset)))
      ((src ↦ᵣ source) ** (dst ↦ᵣ target) ** (tmp ↦ᵣ oldTmp) **
        (source + signExtend12 offset ↦ₘ value) ** (target + signExtend12 offset ↦ₘ old))
      ((src ↦ᵣ source) ** (dst ↦ᵣ target) ** (tmp ↦ᵣ value) **
        (source + signExtend12 offset ↦ₘ value) ** (target + signExtend12 offset ↦ₘ value)) := by
  have load := ld_spec_within tmp src source oldTmp value offset base htmp
  have save := sd_spec_within dst tmp target value old offset (base + 4)
  runBlock load save

theorem copyCheckpoint_spec (src dst tmp : Reg) (base source target oldTmp : Word)
    (value old : Checkpoint) (htmp : tmp ≠ .x0) (_hregs : [src, dst, tmp].Nodup) :
    cpsTripleWithin (copyCheckpoint src dst tmp).length base (base + 40)
      (CodeReq.ofProg base (copyCheckpoint src dst tmp))
      ((src ↦ᵣ source) ** (dst ↦ᵣ target) ** (tmp ↦ᵣ oldTmp) ** value.owns source ** old.owns target)
      ((src ↦ᵣ source) ** (dst ↦ᵣ target) ** (tmp ↦ᵣ value.root.w3) ** value.owns source ** value.owns target) := by
  unfold copyCheckpoint Checkpoint.owns
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have s0 := copyWord_spec src dst tmp base source target oldTmp value.epoch old.epoch 0 htmp
  have s1 := copyWord_spec src dst tmp (base + 8) source target value.epoch value.root.w0 old.root.w0 8 htmp
  have s2 := copyWord_spec src dst tmp (base + 16) source target value.root.w0 value.root.w1 old.root.w1 16 htmp
  have s3 := copyWord_spec src dst tmp (base + 24) source target value.root.w1 value.root.w2 old.root.w2 24 htmp
  have s4 := copyWord_spec src dst tmp (base + 32) source target value.root.w2 value.root.w3 old.root.w3 32 htmp
  runBlock s0 s1 s2 s3 s4

theorem copyRoot_spec (src dst tmp : Reg) (base source target oldTmp : Word)
    (value old : Root) (htmp : tmp ≠ .x0) (_hregs : [src, dst, tmp].Nodup) :
    cpsTripleWithin (copyRoot src dst tmp).length base (base + 32)
      (CodeReq.ofProg base (copyRoot src dst tmp))
      ((src ↦ᵣ source) ** (dst ↦ᵣ target) ** (tmp ↦ᵣ oldTmp) ** value.owns source ** old.owns target)
      ((src ↦ᵣ source) ** (dst ↦ᵣ target) ** (tmp ↦ᵣ value.w3) ** value.owns source ** value.owns target) := by
  unfold copyRoot Root.owns
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, List.length_cons, List.length_nil]
  have s0 := copyWord_spec src dst tmp base source target oldTmp value.w0 old.w0 0 htmp
  have s1 := copyWord_spec src dst tmp (base + 8) source target value.w0 value.w1 old.w1 8 htmp
  have s2 := copyWord_spec src dst tmp (base + 16) source target value.w1 value.w2 old.w2 16 htmp
  have s3 := copyWord_spec src dst tmp (base + 24) source target value.w2 value.w3 old.w3 24 htmp
  runBlock s0 s1 s2 s3

end ClAsm
