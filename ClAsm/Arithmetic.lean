import ClAsm.Layout

namespace ClAsm.Arithmetic

open RiscvZkvm.Rv64

/-- Saturating subtraction at genesis, with one destination register. -/
def previousEpoch (src dst : Reg) : Program :=
  [.SLTIU dst src 1, .ADD dst src dst, .ADDI dst dst 4095]

def previousValue (epoch : Word) : Word :=
  epoch + (if BitVec.ult epoch 1 then 1 else 0) + signExtend12 4095

def shiftJustificationBits (bits : Reg) : Program :=
  [.SLLI bits bits 1, .ANDI bits bits 15]

def shiftedBits (bits : Word) : Word := (bits <<< (1 : Nat)) &&& 15

/-- Inputs are preserved; triple and twice are scratch registers, with the
    canonical boolean result replacing triple. Products must not overflow. -/
def hasSupermajority (vote total triple twice : Reg) : Program :=
  [.SLLI triple vote 1, .ADD triple triple vote, .SLLI twice total 1,
    .SLTU triple triple twice, .XORI triple triple 1]

def thresholdValue (vote total : Word) : Word :=
  (if BitVec.ult ((vote <<< (1 : Nat)) + vote) (total <<< (1 : Nat)) then 1 else 0) ^^^ 1

/-- Since (epoch * 32) mod 8192 = (epoch mod 256) * 32, the root's byte
    offset is (epoch mod 256) * 1024. Mask before shifting to avoid overflow. -/
def blockRootAddress (epoch roots dst : Reg) : Program :=
  [.ANDI dst epoch 255, .SLLI dst dst 10, .ADD dst roots dst]

def rootOffset (epoch : Word) : Word := (epoch &&& 255) <<< (10 : Nat)

end ClAsm.Arithmetic
