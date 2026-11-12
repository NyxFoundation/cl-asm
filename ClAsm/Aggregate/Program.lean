import ClAsm.Aggregate.State
import ClAsm.Arithmetic
import ClAsm.EpochAtSlot
import RiscvZkvm.Rv64.Logic.ControlFlow

namespace ClAsm.Aggregate

open RiscvZkvm.Rv64

/-- Registers the routine may leave clobbered; x14 (slot) and x15 (scratch
    base) are preserved, matching the caller-saved ABI. -/
def temporaries : List Reg :=
  [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x16, .x17, .x28, .x29, .x30, .x31]

/-- Prologue: zero the accumulators, derive E and the previous epoch, and
    materialize the effective-balance increment. -/
def prologue : Program :=
  [.ADDI .x17 .x0 0, .ADDI .x29 .x0 0, .ADDI .x30 .x0 0, .SRLI .x16 .x14 5] ++
    Arithmetic.previousEpoch .x16 .x31 ++
    [.LUI .x28 0x3B9AD, .ADDI .x28 .x28 0xA00]

/-- The fold of an active validator's effective balance into one accumulator. -/
def activeFold (epoch acc : Reg) : Program :=
  [.LD .x5 .x10 8, .LD .x6 .x10 16, .SLTU .x7 epoch .x5, .XORI .x7 .x7 1,
    .SLTU .x5 epoch .x6, .AND .x5 .x5 .x7, .LD .x6 .x10 0, .SUB .x7 .x0 .x5,
    .AND .x6 .x6 .x7, .ADD acc acc .x6]

/-- The fold of one target-flag contribution: active, unslashed, flagged. -/
def targetFold (epoch flags acc : Reg) : Program :=
  [.LD .x5 .x10 8, .LD .x6 .x10 16, .SLTU .x7 epoch .x5, .XORI .x7 .x7 1,
    .SLTU .x5 epoch .x6, .AND .x5 .x5 .x7, .LD .x6 .x10 24, .SLTU .x6 .x0 .x6,
    .XORI .x6 .x6 1, .AND .x5 .x5 .x6, .LD .x6 flags 0, .ANDI .x6 .x6 2,
    .SLTU .x6 .x0 .x6, .AND .x5 .x5 .x6, .LD .x6 .x10 0, .SUB .x7 .x0 .x5,
    .AND .x6 .x6 .x7, .ADD acc acc .x6]

/-- The pointer and counter advance after processing one validator. -/
def walk : Program :=
  [.ADDI .x10 .x10 32, .ADDI .x11 .x11 8, .ADDI .x12 .x12 8, .ADDI .x13 .x13 4095]

/-- One iteration over the validator the pointers address. -/
def bodyStraight : Program :=
  activeFold .x16 .x17 ++ targetFold .x31 .x11 .x29 ++ targetFold .x16 .x12 .x30 ++ walk

/-- The guarded loop: guard, body, and the jump back to the guard. -/
def loopBackOffset : BitVec 21 :=
  BitVec.ofInt 21 (-(4 * (2 + bodyStraight.length) : Int))
def loopExitOffset : BitVec 21 := 4 * (bodyStraight.length + 2)

def loopGuard : Program := [.BNE .x13 .x0 8, .JAL .x0 loopExitOffset]
def backJal : Program := [.JAL .x0 loopBackOffset]

def loop : Program := loopGuard ++ bodyStraight ++ backJal

def saturateOne (reg : Reg) (offset : BitVec 12) : Program :=
  [.SLTU .x5 reg .x28] ++ if_eq .x5 .x0 [.SD .x15 reg offset] [.SD .x15 .x28 offset]

/-- Store each saturated balance or the increment floor, then return. -/
def epilogue : Program :=
  saturateOne .x17 0 ++ saturateOne .x29 8 ++ saturateOne .x30 16 ++ [.JALR .x0 .x1 0]

def program : Program := prologue ++ loop ++ epilogue

/-- The step count for `n` admitted validators is bounded by this function. -/
def stepBound (n : Nat) : Nat := 52 * n + 24

theorem prologue_length : prologue.length = 9 := by rfl
theorem bodyStraight_length : bodyStraight.length = 50 := by rfl
theorem loopGuard_length : loopGuard.length = 2 := by decide
theorem backJal_length : backJal.length = 1 := by rfl
theorem epilogue_length : epilogue.length = 16 := by decide
theorem program_length : program.length = 78 := by decide

theorem loopBack_word :
    signExtend21 (BitVec.ofInt 21 (-(208 : Int))) = BitVec.ofNat 64 (2^64 - 208) := by
  simp only [signExtend21]
  bv_decide

/-- The back jump lands exactly on the loop guard. -/
theorem loopBackOffset_value : loopBackOffset = BitVec.ofInt 21 (-(208 : Int)) := by
  show BitVec.ofInt 21 (-(4 * (2 + bodyStraight.length) : Int)) = _
  rw [bodyStraight_length]
  rfl

theorem loopBackTarget (branch head : Word) (hbranch : branch = head + BitVec.ofNat 64 208) :
    branch + signExtend21 loopBackOffset = head := by
  rw [hbranch, loopBackOffset_value, loopBack_word]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem loopExit_word :
    signExtend21 loopExitOffset = BitVec.ofNat 64 (4 * (bodyStraight.length + 2)) := by
  simp only [loopExitOffset, signExtend21, bodyStraight_length]
  bv_decide

/-- The guard's second instruction jumps into the epilogue. -/
theorem loopExitTarget (head : Word) :
    (head + BitVec.ofNat 64 4) + signExtend21 loopExitOffset =
      head + BitVec.ofNat 64 (4 + 4 * (bodyStraight.length + 2)) := by
  rw [loopExit_word, BitVec.add_assoc, ofNat_add_le 4 (4 * (bodyStraight.length + 2))
    (by have := bodyStraight_length; omega)]

end ClAsm.Aggregate
