import ClAsm.Layout
import RiscvZkvm.Rv64.Logic.SepLogic

namespace ClAsm

open RiscvZkvm.Rv64

/-- Four little-endian memory words preserve a root's 32 bytes exactly. -/
structure Root where
  w0 : Word
  w1 : Word
  w2 : Word
  w3 : Word
  deriving Repr, DecidableEq, BEq

structure Checkpoint where
  epoch : Word
  root : Root
  deriving Repr, DecidableEq, BEq

def Root.owns (ptr : Word) (root : Root) : Assertion :=
  (ptr + signExtend12 0 ↦ₘ root.w0) ** (ptr + signExtend12 8 ↦ₘ root.w1) **
    (ptr + signExtend12 16 ↦ₘ root.w2) ** (ptr + signExtend12 24 ↦ₘ root.w3)

def Checkpoint.owns (ptr : Word) (checkpoint : Checkpoint) : Assertion :=
  (ptr + signExtend12 0 ↦ₘ checkpoint.epoch) ** (ptr + signExtend12 8 ↦ₘ checkpoint.root.w0) **
    (ptr + signExtend12 16 ↦ₘ checkpoint.root.w1) ** (ptr + signExtend12 24 ↦ₘ checkpoint.root.w2) **
    (ptr + signExtend12 32 ↦ₘ checkpoint.root.w3)

/-- Copy distinct 40-byte checkpoint regions, preserving the source and pointers. -/
def copyCheckpoint (src dst tmp : Reg) : Program :=
  [.LD tmp src 0, .SD dst tmp 0, .LD tmp src 8, .SD dst tmp 8,
    .LD tmp src 16, .SD dst tmp 16, .LD tmp src 24, .SD dst tmp 24,
    .LD tmp src 32, .SD dst tmp 32]

/-- Read and copy a selected root without interpreting its bytes. -/
def copyRoot (src dst tmp : Reg) : Program :=
  [.LD tmp src 0, .SD dst tmp 0, .LD tmp src 8, .SD dst tmp 8,
    .LD tmp src 16, .SD dst tmp 16, .LD tmp src 24, .SD dst tmp 24]

end ClAsm
