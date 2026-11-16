import ClAsm.EpochAtSlot
import RiscvZkvm.Rv64.Logic.ControlFlow

namespace ClAsm.Progress

open RiscvZkvm.Rv64

/-- Registers the routine may leave clobbered; x10 (validator count) and x14
    (slot) are preserved, matching the internal ABI. -/
def temporaries : List Reg :=
  [.x5, .x6, .x7, .x11, .x12, .x13, .x16, .x17, .x18, .x19, .x20]

/-- process_eth1_data_reset: reset the eth1 vote record when the next epoch
    starts a voting period.  x16 holds the epoch derived from the slot. -/
def eth1Reset : Program :=
  [.SRLI .x16 .x14 5, .ADDI .x17 .x16 1, .ANDI .x17 .x17 63,
    .LUI .x18 0x74000, .BNE .x17 .x0 8, .SD .x18 .x0 0]

/-- process_slashings_reset: slashings[next_epoch % 8192] = 0. -/
def slashingsReset : Program :=
  [.ADDI .x17 .x16 1, .LUI .x18 0x2, .ADDI .x18 .x18 4095, .AND .x17 .x17 .x18,
    .SLLI .x17 .x17 3, .LUI .x19 0x73000, .ADD .x17 .x17 .x19, .SD .x17 .x0 0]

/-- process_randao_mixes_reset: copy the current-epoch mix into the next-epoch
    slot of the 65536-entry randao mix vector. -/
def randaoReset : Program :=
  [.LUI .x18 0x10, .ADDI .x18 .x18 4095, .ADDI .x17 .x16 0, .AND .x17 .x17 .x18,
    .SLLI .x17 .x17 3, .LUI .x19 0x72000, .ADD .x17 .x17 .x19, .LD .x5 .x17 0,
    .ADDI .x20 .x16 1, .AND .x20 .x20 .x18, .SLLI .x20 .x20 3, .ADD .x20 .x20 .x19,
    .SD .x20 .x5 0]

/-- process_participation_flag_updates prologue: current count into x13 and the
    participation array bases into x11 and x12. -/
def rotPrologue : Program := [.ADDI .x13 .x10 0, .LUI .x11 0x70000, .LUI .x12 0x71000]

/-- The pointer and counter advance after rotating one validator's flags. -/
def rotBody : Program :=
  [.LD .x5 .x12 0, .SD .x11 .x5 0, .SD .x12 .x0 0,
    .ADDI .x11 .x11 8, .ADDI .x12 .x12 8, .ADDI .x13 .x13 4095]

def rotBackOffset : BitVec 21 :=
  BitVec.ofInt 21 (-(4 * (2 + rotBody.length) : Int))
def rotExitOffset : BitVec 21 := 4 * (rotBody.length + 2)

def rotGuard : Program := [.BNE .x13 .x0 8, .JAL .x0 rotExitOffset]
def rotBack : Program := [.JAL .x0 rotBackOffset]

/-- The guarded rotation loop: guard, body, jump back to the guard. -/
def rotLoop : Program := rotGuard ++ rotBody ++ rotBack

def program : Program :=
  eth1Reset ++ slashingsReset ++ randaoReset ++ rotPrologue ++ rotLoop ++ [.JALR .x0 .x1 0]

/-- The step count for a routine admitting `n` participation entries is bounded
    by this function. -/
def stepBound (n : Nat) : Nat := 8 * n + 33

theorem eth1Reset_length : eth1Reset.length = 6 := by rfl
theorem slashingsReset_length : slashingsReset.length = 8 := by rfl
theorem randaoReset_length : randaoReset.length = 13 := by rfl
theorem rotPrologue_length : rotPrologue.length = 3 := by rfl
theorem rotBody_length : rotBody.length = 6 := by rfl
theorem rotLoop_length : rotLoop.length = 9 := by rfl
theorem program_length : program.length = 40 := by decide

theorem rotBack_word :
    signExtend21 (BitVec.ofInt 21 (-(32 : Int))) = BitVec.ofNat 64 (2^64 - 32) := by
  simp only [signExtend21]
  bv_decide

/-- The back jump lands exactly on the loop guard. -/
theorem rotBackOffset_value : rotBackOffset = BitVec.ofInt 21 (-(32 : Int)) := by
  show BitVec.ofInt 21 (-(4 * (2 + rotBody.length) : Int)) = _
  rw [rotBody_length]
  rfl

theorem rotBackTarget (branch head : Word) (hbranch : branch = head + BitVec.ofNat 64 32) :
    branch + signExtend21 rotBackOffset = head := by
  rw [hbranch, rotBackOffset_value, rotBack_word]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem rotExit_word :
    signExtend21 rotExitOffset = BitVec.ofNat 64 (4 * (rotBody.length + 2)) := by
  simp only [rotExitOffset, signExtend21, rotBody_length]
  bv_decide

/-- The guard's second instruction jumps past the loop. -/
theorem rotExitTarget (head : Word) :
    (head + BitVec.ofNat 64 4) + signExtend21 rotExitOffset =
      head + BitVec.ofNat 64 (4 + 4 * (rotBody.length + 2)) := by
  rw [rotExit_word, BitVec.add_assoc]
  rfl

end ClAsm.Progress
