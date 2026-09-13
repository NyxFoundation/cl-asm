import ClAsm.Arithmetic
import ClAsm.EpochAtSlot
import ClAsm.Checkpoint
import RiscvZkvm.Rv64.Logic.ControlFlow

namespace ClAsm.Weigh

open RiscvZkvm.Rv64

/-- Preserve all ABI arguments; use only caller-saved temporaries. -/
def temporaries : List Reg := [.x5, .x6, .x7, .x16, .x17, .x28, .x29, .x30, .x31]

/-- Save old checkpoints before replacing previous with old current. -/
def prologue : Program :=
  [.ADDI .x6 .x10 16, .ADDI .x7 .x15 0] ++ copyCheckpoint .x6 .x7 .x5 ++
  [.ADDI .x6 .x10 56, .ADDI .x7 .x15 40] ++ copyCheckpoint .x6 .x7 .x5 ++
  [.ADDI .x7 .x10 16] ++ copyCheckpoint .x6 .x7 .x5 ++
  EpochAtSlot.program .x10 .x16 ++ Arithmetic.previousEpoch .x16 .x17 ++
  [.LD .x28 .x10 8] ++ Arithmetic.shiftJustificationBits .x28

/-- A successful threshold updates current and sets the corresponding bit. -/
def justifyBody (epoch : Reg) (bit : BitVec 12) : Program :=
  [.SD .x10 epoch 56] ++ Arithmetic.blockRootAddress epoch .x11 .x6 ++
  [.ADDI .x7 .x10 64] ++ copyRoot .x6 .x7 .x5 ++ [.ORI .x28 .x28 bit]

def justify (vote epoch : Reg) (bit : BitVec 12) : Program :=
  Arithmetic.hasSupermajority vote .x12 .x29 .x30 ++
  if_eq .x29 .x0 [] (justifyBody epoch bit)

/-- Form one canonical boolean from the bit mask and saved epoch equality. -/
def finalizationCondition (offset delta mask : BitVec 12) : Program :=
  [.ANDI .x29 .x28 mask, .XORI .x29 .x29 mask, .SLTIU .x29 .x29 1,
    .LD .x31 .x15 offset, .ADDI .x31 .x31 delta, .XOR .x31 .x31 .x16,
    .SLTIU .x31 .x31 1, .AND .x29 .x29 .x31]

def finalizeBody (offset : BitVec 12) : Program :=
  [.ADDI .x6 .x15 offset, .ADDI .x7 .x10 96] ++ copyCheckpoint .x6 .x7 .x5

def finalize (offset delta mask : BitVec 12) : Program :=
  finalizationCondition offset delta mask ++ if_eq .x29 .x0 [] (finalizeBody offset)

/-- The four finalizations deliberately remain independent, ordered updates. -/
def program : Program :=
  prologue ++ justify .x13 .x17 2 ++ justify .x14 .x16 1 ++
  finalize 0 3 14 ++ finalize 0 2 6 ++ finalize 40 2 7 ++ finalize 40 1 3 ++
  [.SD .x10 .x28 8, .JALR .x0 .x1 0]

/-- All branches are forward; the instruction count is a conservative bound. -/
def stepBound : Nat := program.length

set_option maxRecDepth 4096 in
theorem program_length : program.length = 175 := by decide

end ClAsm.Weigh
