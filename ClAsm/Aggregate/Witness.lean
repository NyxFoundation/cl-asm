import ClAsm.Aggregate.Proof
import ClAsm.Weigh.RegisterWitness

namespace ClAsm.Aggregate

open RiscvZkvm.Rv64

def witnessAddresses : Addresses :=
  ⟨BitVec.ofNat 64 entry, BitVec.ofNat 64 returnAddress,
    BitVec.ofNat 64 validatorsAddress, BitVec.ofNat 64 previousFlagsAddress,
    BitVec.ofNat 64 currentFlagsAddress, BitVec.ofNat 64 scratchAddress⟩

def witnessInput : Input := ⟨0, [], [], []⟩
def witnessRegisters : Registers := {}

def witness : MachineState where
  regs := fun r => match r with
    | .x1 => witnessAddresses.returnAddress
    | .x10 => witnessAddresses.validators
    | .x11 => witnessAddresses.previousFlags
    | .x12 => witnessAddresses.currentFlags
    | .x15 => witnessAddresses.scratch
    | _ => 0
  mem := fun _ => 0
  code := CodeReq.ofProg witnessAddresses.entry program
  pc := witnessAddresses.entry

theorem witness_addresses : ValidAddresses witnessAddresses 0 := by
  constructor <;> try decide
  all_goals unfold disjointRanges; decide

theorem witness_input : ValidInput witnessInput := by
  constructor <;> simp [witnessInput, sumActive, sumTarget, sumTargetPairs]

private theorem witness_memory :
    Weigh.MemoryWitness (scratchOwn witnessAddresses 0 0 0) scratchAddress (scratchAddress + 24) := by
  have cells := Weigh.zeroCells_witness scratchAddress 3 (by decide) (by decide) (by decide)
  simpa [scratchOwn, witnessAddresses, Weigh.zeroCells, signExtend12,
    scratchAddress, sepConj_emp_right'] using cells

private def witnessRegList : List Reg :=
  [.x5, .x6, .x7, .x16, .x17, .x28, .x29, .x30, .x31,
    .x0, .x1, .x14, .x15, .x10, .x11, .x12, .x13]

theorem witness_pre :
    (precondition witnessAddresses witnessInput witnessRegisters 0 0 0).holdsFor witness := by
  have h := Weigh.registers_memory_compatible witness witnessRegList
    (scratchOwn witnessAddresses 0 0 0) (by decide) (by intro; rfl) witness_memory
  simpa [precondition, witnessRegisters, Registers.owns, callRegisters, arraysOwn,
    validatorsOwn, wordsOwn, witnessInput, Weigh.registerCells, witnessRegList,
    witness, MachineState.getReg, sepConj_emp_right', sepConj_emp_left', sepConj_assoc'] using h

theorem witness_returns :
    ∃ steps, steps ≤ stepBound 0 ∧ ∃ final,
      stepN steps witness = some final ∧ final.pc = witnessAddresses.returnAddress ∧
      (postcondition witnessAddresses witnessInput).holdsFor final := by
  have spec := program_spec witnessAddresses witnessInput witnessRegisters 0 0 0
    witness_addresses witness_input
  simpa only [sepConj_emp_right', witnessInput, List.length_nil] using
    spec empAssertion pcFree_emp witness (fun _ _ instruction => instruction)
      (by simpa only [sepConj_emp_right'] using witness_pre) rfl

end ClAsm.Aggregate
