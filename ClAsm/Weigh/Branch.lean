import ClAsm.Weigh.Program
import RiscvZkvm.Rv64.Logic.SyscallSpecs
import RiscvZkvm.Rv64.Logic.Tactics.RunBlock

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

/-- The empty-then branch used by both conditional updates. -/
theorem branchNonzero_spec (base value : Word) :
    cpsTripleWithin 1 base (if value = 0 then base + 4 else base + 8)
      (CodeReq.singleton base (.BNE .x29 .x0 8))
      ((.x29 ↦ᵣ value) ** (.x0 ↦ᵣ 0)) ((.x29 ↦ᵣ value) ** (.x0 ↦ᵣ 0)) := by
  intro F hF s hcode hpre hpc
  have hfetch : s.code s.pc = some (.BNE .x29 .x0 8) := by
    rw [hpc]
    exact CodeReq.singleton_satisfiedBy.mp hcode
  have hp := holdsFor_sepConj_elim_left hpre
  have hv := holdsFor_regIs.mp (holdsFor_sepConj_elim_left hp)
  have hz := holdsFor_regIs.mp (holdsFor_sepConj_elim_right hp)
  have hs := step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl)
  have hexec : execInstrBr s (.BNE .x29 .x0 8) =
      s.setPC (if value = 0 then base + 4 else base + 8) := by
    by_cases h : value = 0 <;>
      simp [execInstrBr, hv, hz, bne_iff_ne, h, hpc, signExtend13] <;> split <;> rfl
  refine ⟨1, Nat.le_refl 1, s.setPC (if value = 0 then base + 4 else base + 8), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hs, hexec]
    rfl
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hF) hpre

end ClAsm.Weigh
