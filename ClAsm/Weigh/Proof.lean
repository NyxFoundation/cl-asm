import ClAsm.Weigh.Execution
import RiscvZkvm.Rv64.Logic.BitAux

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

private theorem return_spec (base ret : Word) (hret : ret &&& 1 = 0) :
    cpsTripleWithin 1 base ret (CodeReq.singleton base (.JALR .x0 .x1 0))
      (.x1 ↦ᵣ ret) (.x1 ↦ᵣ ret) := by
  have jump := jalr_x0_spec_gen_within .x1 ret 0 base
  have target : (ret + signExtend12 0) &&& ~~~(1 : Word) = ret := by
    simpa [signExtend12] using BitAux.word_andn_one_of_even hret
  rw [target] at jump
  exact jump

/-- Extend a block by its checked instruction slice, without enumerating every
    pair of code addresses during separation-logic composition. -/
private theorem extendProgram {n : Nat} {base entry exit : Word} {block : Program} {P Q : Assertion}
    (index : Nat) (ha : entry = base + BitVec.ofNat 64 (4 * index))
    (hs : (program.drop index).take block.length = block) (hr : index + block.length ≤ program.length)
    (spec : cpsTripleWithin n entry exit (CodeReq.ofProg entry block) P Q) :
    cpsTripleWithin n entry exit (CodeReq.ofProg base program) P Q :=
  cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base entry program block index ha hs hr (by rw [program_length]; decide)) spec

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem program_execution_spec (a : Addresses) (state : State) (balances : Balances) (r : Registers)
    (roots : RootArray) (scratch0 scratch1 : Checkpoint) (hret : a.returnAddress &&& 1 = 0) :
    cpsTripleWithin stepBound a.entry a.returnAddress (CodeReq.ofProg a.entry program)
      (precondition a state balances r roots scratch0 scratch1)
      ((executionResult a state balances r roots).1.owns a balances **
        (executionResult a state balances r roots).2.owns a.state **
        rootsOwn a.roots (List.ofFn roots) ** state.previous.owns a.scratch **
        state.current.owns (a.scratch + 40)) := by
  haveI : Assertion.PCFree (rootsOwn a.roots (List.ofFn roots)) :=
    ⟨rootsOwn_pcFree a.roots (List.ofFn roots)⟩
  let r0 := { r with prologue := prologueRegisters a.state state }
  let r1 := justifyRegisters a balances r0 roots false
  let r2 := justifyRegisters a balances r1 roots true
  let r3 := finalizeRegisters a r2 state.previous 0 3 14
  let r4 := finalizeRegisters a r3 state.previous 0 2 6
  let r5 := finalizeRegisters a r4 state.current 40 2 7
  let r6 := finalizeRegisters a r5 state.current 40 1 3
  let c1 := justifiedCheckpoint balances r0 roots false state.current
  let f1 := finalizationCheckpoint r2 state.previous state.finalized 3 14
  let f2 := finalizationCheckpoint r3 state.previous f1 2 6
  let f3 := finalizationCheckpoint r4 state.current f2 2 7
  have p := prologue_spec a.entry a.state a.scratch state r.prologue scratch0 scratch1
  have j1 := justify_spec (a.entry + 172) a balances r0 roots state.current false
  have j2 := justify_spec (a.entry + 256) a balances r1 roots c1 true
  have b1 := finalize_spec (a.entry + 340) a balances r2 state.previous state.finalized 0 3 14
  have b2 := finalize_spec (a.entry + 428) a balances r3 state.previous f1 0 2 6
  have b3 := finalize_spec (a.entry + 516) a balances r4 state.current f2 40 2 7
  have b4 := finalize_spec (a.entry + 604) a balances r5 state.current f3 40 1 3
  have store := sd_spec_within .x10 .x28 a.state r6.prologue.bits state.bits 8 (a.entry + 692)
  have ret := return_spec (a.entry + 696) a.returnAddress hret
  rw [← CodeReq.ofProg_singleton] at store ret
  have p := extendProgram (base := a.entry) 0 (by simp) (by decide) (by decide) p
  have j1 := extendProgram (base := a.entry) 43 rfl (by decide) (by decide) j1
  have j2 := extendProgram (base := a.entry) 64 rfl (by decide) (by decide) j2
  have b1 := extendProgram (base := a.entry) 85 rfl (by decide) (by decide) b1
  have b2 := extendProgram (base := a.entry) 107 rfl (by decide) (by decide) b2
  have b3 := extendProgram (base := a.entry) 129 rfl (by decide) (by decide) b3
  have b4 := extendProgram (base := a.entry) 151 rfl (by decide) (by decide) b4
  have store := extendProgram (base := a.entry) 173 rfl (by decide) (by decide) store
  have ret := extendProgram (base := a.entry) 174 rfl (by decide) (by decide) ret
  generalize hcode : CodeReq.ofProg a.entry program = code at p j1 j2 b1 b2 b3 b4 store ret ⊢
  unfold precondition executionResult justificationResult finalizationResult
  simp only [stepBound, program_length, show prologue.length = 43 from rfl,
    show (finalize 0 3 14).length = 22 from rfl, show (finalize 0 2 6).length = 22 from rfl,
    show (finalize 40 2 7).length = 22 from rfl, show (finalize 40 1 3).length = 22 from rfl,
    Registers.owns, PrologueRegisters.owns, State.owns, Checkpoint.owns] at p j1 j2 b1 b2 b3 b4 ⊢
  dsimp only [f1, f2, f3, finalizationCheckpoint] at b2 b3 b4 ⊢
  runBlock p j1 j2 b1 b2 b3 b4 store ret

end ClAsm.Weigh
