import ClAsm.Weigh.RegisterWitness
import ClAsm.Weigh.Correctness

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

set_option maxRecDepth 4096

def witnessAddresses : Addresses :=
  ⟨BitVec.ofNat 64 Layout.entry, BitVec.ofNat 64 Layout.stateAddress,
    BitVec.ofNat 64 Layout.rootsAddress, BitVec.ofNat 64 Layout.scratchAddress,
    BitVec.ofNat 64 Layout.returnAddress⟩

def witnessState : State := ⟨0, 0, zeroCheckpoint, zeroCheckpoint, zeroCheckpoint⟩
def witnessBalances : Balances := ⟨1, 0, 0⟩
def witnessRegisters : Registers := ⟨⟨0, 0, 0, 0, 0, 0⟩, 0, 0, 0⟩
def witnessRoots : RootArray := fun _ => zeroRoot

/-- A complete call with all three allocated data regions and executable code. -/
def witness : MachineState where
  regs := fun r => match r with
    | .x1 => witnessAddresses.returnAddress
    | .x10 => witnessAddresses.state
    | .x11 => witnessAddresses.roots
    | .x12 => 1
    | .x15 => witnessAddresses.scratch
    | _ => 0
  mem := fun _ => 0
  code := CodeReq.ofProg witnessAddresses.entry program
  pc := witnessAddresses.entry

theorem witness_addresses : ValidAddresses witnessAddresses := by
  constructor <;> try decide
  all_goals unfold disjointRanges; decide

theorem witness_input : ValidInput witnessState witnessBalances := by
  constructor <;> try decide
  all_goals intro h; simp [threshold, witnessBalances] at h

private theorem witness_state_cells (start : Nat) :
    witnessState.owns (BitVec.ofNat 64 start) = zeroCells start 17 := by
  simp [witnessState, State.owns, zeroCheckpoint, zeroRoot, Checkpoint.owns, zeroCells,
    signExtend12, BitVec.ofNat_add, BitVec.add_assoc, sepConj_emp_right', sepConj_assoc']

private def witnessData : Assertion :=
  witnessState.owns witnessAddresses.state ** rootsOwn witnessAddresses.roots (List.ofFn witnessRoots) **
    zeroCheckpoint.owns witnessAddresses.scratch ** zeroCheckpoint.owns (witnessAddresses.scratch + 40)

private theorem witness_root_list : List.ofFn witnessRoots =
    List.replicate Layout.slotsPerHistoricalRoot zeroRoot := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [witnessRoots]

private theorem witness_memory : MemoryWitness witnessData Layout.stateAddress (Layout.scratchAddress + 80) := by
  have hs := zeroCells_witness Layout.stateAddress 17 (by decide) (by decide) (by decide)
  have hr := zeroCells_witness Layout.rootsAddress (4 * Layout.slotsPerHistoricalRoot)
    (by decide) (by decide) (by decide)
  have hc := zeroCells_witness Layout.scratchAddress 10 (by decide) (by decide) (by decide)
  have hrc := memoryWitness_sep
    (memoryWitness_widen hr (Nat.le_refl _) (show Layout.rootsAddress +
      8 * (4 * Layout.slotsPerHistoricalRoot) ≤ Layout.scratchAddress by decide)) hc (by decide) (by decide)
  have h := memoryWitness_sep
    (memoryWitness_widen hs (Nat.le_refl _)
      (show Layout.stateAddress + 8 * 17 ≤ Layout.rootsAddress by decide)) hrc (by decide) (by decide)
  simpa only [witnessData, witnessAddresses, witness_root_list, witness_state_cells,
    rootsOwn_zero_cells, show (BitVec.ofNat 64 Layout.scratchAddress : Word) + 40 =
      BitVec.ofNat 64 (Layout.scratchAddress + 40) from by decide,
    zeroCheckpoint_cells, show (10 : Nat) = 5 + 5 from rfl, zeroCells_append] using h

def witnessRegList : List Reg :=
  [.x0, .x1, .x11, .x12, .x13, .x14, .x10, .x15, .x5, .x6, .x7, .x16, .x17, .x28, .x29, .x30, .x31]

theorem witness_pre :
    (precondition witnessAddresses witnessState witnessBalances witnessRegisters witnessRoots
      zeroCheckpoint zeroCheckpoint).holdsFor witness := by
  have h := registers_memory_compatible witness witnessRegList witnessData (by decide) (by intro; rfl)
    witness_memory
  simpa [precondition, witnessRegisters, Registers.owns, PrologueRegisters.owns, witnessData,
    registerCells, witnessRegList, witness, MachineState.getReg, witnessBalances,
    sepConj_emp_right', sepConj_assoc'] using h

theorem witness_code : (CodeReq.ofProg witnessAddresses.entry program).SatisfiedBy witness :=
  fun _ _ instruction => instruction

theorem witness_return_outside : witness.code witnessAddresses.returnAddress = none := by decide

theorem witness_returns :
    ∃ steps, steps ≤ stepBound ∧ ∃ final,
      stepN steps witness = some final ∧ final.pc = witnessAddresses.returnAddress ∧
      (postcondition witnessAddresses witnessState witnessBalances witnessRoots).holdsFor final := by
  have spec := program_spec witnessAddresses witnessState witnessBalances witnessRegisters witnessRoots
    zeroCheckpoint zeroCheckpoint witness_addresses witness_input
  simpa only [sepConj_emp_right'] using
    spec empAssertion (by pcFree) witness witness_code
      (by simpa only [sepConj_emp_right'] using witness_pre) rfl

end ClAsm.Weigh
