import ClAsm.Layout

namespace ClAsm.EpochAtSlot

open RiscvZkvm.Rv64

/-- Inline helper: read slot through the state pointer and write its epoch to dst.
    The contract requires distinct registers, with dst different from x0. -/
def program (state dst : Reg) : Program :=
  [.LD dst state 0, .SRLI dst dst 5]

/-- Callable probe of the helper using the planned weigh ABI's state pointer.
    x5 is caller-saved; x10 retains the state pointer. -/
def callable : Program := program .x10 .x5 ++ [.JALR .x0 .x1 0]

def stepBound : Nat := callable.length

def epoch (slot : Word) : Word := slot >>> (5 : Nat)

theorem epoch_toNat (slot : Word) :
    (epoch slot).toNat = slot.toNat / Layout.slotsPerEpoch := by
  simp [epoch, Layout.slotsPerEpoch, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end ClAsm.EpochAtSlot
