import ClAsm.EpochAtSlot.Proof

namespace ClAsm.EpochAtSlot

open RiscvZkvm.Rv64

/-- A concrete valid call, with code placement and a return outside the routine. -/
def witness : MachineState where
  regs := fun r => match r with
    | .x10 => BitVec.ofNat 64 Layout.stateAddress
    | .x1 => BitVec.ofNat 64 Layout.returnAddress
    | _ => 0
  mem := fun a => if a == BitVec.ofNat 64 Layout.stateAddress then 64 else 0
  code := CodeReq.ofProg (BitVec.ofNat 64 Layout.entry) callable
  pc := BitVec.ofNat 64 Layout.entry

private def pointerResource : PartialState :=
  .singletonReg .x10 (BitVec.ofNat 64 Layout.stateAddress)
private def resultResource : PartialState := .singletonReg .x5 0
private def slotResource : PartialState :=
  .singletonMem (BitVec.ofNat 64 Layout.stateAddress) 64
private def returnResource : PartialState :=
  .singletonReg .x1 (BitVec.ofNat 64 Layout.returnAddress)

private theorem slot_return_disjoint : slotResource.Disjoint returnResource := by
  simp [slotResource, returnResource, PartialState.Disjoint,
    PartialState.singletonMem, PartialState.singletonReg]

private theorem result_disjoint :
    resultResource.Disjoint (slotResource.union returnResource) := by
  simp [resultResource, slotResource, returnResource, PartialState.Disjoint,
    PartialState.singletonMem, PartialState.singletonReg, PartialState.union]
  intro r; cases r <;> simp

private theorem pointer_disjoint :
    pointerResource.Disjoint (resultResource.union (slotResource.union returnResource)) := by
  simp [pointerResource, resultResource, slotResource, returnResource, PartialState.Disjoint,
    PartialState.singletonMem, PartialState.singletonReg, PartialState.union]
  intro r; cases r <;> simp

theorem witness_pre :
    (pre (BitVec.ofNat 64 Layout.stateAddress) 64 0
      (BitVec.ofNat 64 Layout.returnAddress)).holdsFor witness := by
  refine ⟨pointerResource.union (resultResource.union (slotResource.union returnResource)), ?_, ?_⟩
  · rw [PartialState.CompatibleWith_union pointer_disjoint,
      PartialState.CompatibleWith_union result_disjoint,
      PartialState.CompatibleWith_union slot_return_disjoint]
    exact ⟨PartialState.CompatibleWith_singletonReg.mpr rfl,
      PartialState.CompatibleWith_singletonReg.mpr rfl,
      PartialState.CompatibleWith_singletonMem.mpr rfl,
      PartialState.CompatibleWith_singletonReg.mpr rfl⟩
  · exact ⟨pointerResource, _, pointer_disjoint, rfl, rfl,
      resultResource, _, result_disjoint, rfl, rfl,
      slotResource, returnResource, slot_return_disjoint, rfl, ⟨rfl, by decide⟩, rfl⟩

theorem witness_code :
    (CodeReq.ofProg (BitVec.ofNat 64 Layout.entry) callable).SatisfiedBy witness :=
  fun _ _ instruction => instruction

theorem witness_return_outside :
    witness.code (BitVec.ofNat 64 Layout.returnAddress) = none := by decide

/-- Instantiate the frame-aware contract to show that its premises are inhabited. -/
theorem witness_returns :
    ∃ steps, steps ≤ stepBound ∧ ∃ final,
      stepN steps witness = some final ∧ final.pc = BitVec.ofNat 64 Layout.returnAddress ∧
      (post (BitVec.ofNat 64 Layout.stateAddress) 64
        (BitVec.ofNat 64 Layout.returnAddress)).holdsFor final := by
  have spec := callable_spec (BitVec.ofNat 64 Layout.entry)
    (BitVec.ofNat 64 Layout.stateAddress) 64 0 (BitVec.ofNat 64 Layout.returnAddress) (by decide)
  simpa only [sepConj_emp_right'] using
    spec empAssertion (by pcFree) witness witness_code
      (by simpa only [sepConj_emp_right'] using witness_pre) rfl

end ClAsm.EpochAtSlot
