import ClAsm.Weigh.Justification
import ClAsm.Weigh.Finalization

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

def finalizationCheckpoint (r : Registers) (saved old : Checkpoint) (delta mask : BitVec 12) : Checkpoint :=
  if finalizationValue r.prologue.bits saved.epoch r.prologue.epoch delta mask = 0 then old else saved

def justificationResult (a : Addresses) (state : State) (balances : Balances) (r : Registers)
    (roots : RootArray) : Registers × Checkpoint :=
  let r0 := { r with prologue := prologueRegisters a.state state }
  let c1 := justifiedCheckpoint balances r0 roots false state.current
  let r1 := justifyRegisters a balances r0 roots false
  (justifyRegisters a balances r1 roots true, justifiedCheckpoint balances r1 roots true c1)

def finalizationResult (a : Addresses) (state : State) (r : Registers) : Registers × Checkpoint :=
  let f1 := finalizationCheckpoint r state.previous state.finalized 3 14
  let r1 := finalizeRegisters a r state.previous 0 3 14
  let f2 := finalizationCheckpoint r1 state.previous f1 2 6
  let r2 := finalizeRegisters a r1 state.previous 0 2 6
  let f3 := finalizationCheckpoint r2 state.current f2 2 7
  let r3 := finalizeRegisters a r2 state.current 40 2 7
  (finalizeRegisters a r3 state.current 40 1 3, finalizationCheckpoint r3 state.current f3 1 3)

/-- Exact word-level result of executing the emitted instructions. -/
def executionResult (a : Addresses) (state : State) (balances : Balances) (r : Registers)
    (roots : RootArray) : Registers × State :=
  let j := justificationResult a state balances r roots
  let f := finalizationResult a state j.1
  (f.1, { state with
    previous := state.current
    current := j.2
    finalized := f.2
    bits := f.1.prologue.bits })

end ClAsm.Weigh
