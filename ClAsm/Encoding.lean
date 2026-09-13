import RiscvZkvm.Rv64.Program
import Lean.Data.Json

namespace ClAsm.Encoding

open Lean RiscvZkvm.Rv64

/-- Raw modeled operands for a separately implemented test encoder. -/
def describe : Instr → Except String (String × List Int)
  | .LD d a i => .ok ("LD", [d.toNat, a.toNat, i.toInt])
  | .SD a b i => .ok ("SD", [a.toNat, b.toNat, i.toInt])
  | .ADDI d a i => .ok ("ADDI", [d.toNat, a.toNat, i.toInt])
  | .ANDI d a i => .ok ("ANDI", [d.toNat, a.toNat, i.toInt])
  | .ORI d a i => .ok ("ORI", [d.toNat, a.toNat, i.toInt])
  | .XORI d a i => .ok ("XORI", [d.toNat, a.toNat, i.toInt])
  | .SLTIU d a i => .ok ("SLTIU", [d.toNat, a.toNat, i.toInt])
  | .SLLI d a i => .ok ("SLLI", [d.toNat, a.toNat, i.toNat])
  | .SRLI d a i => .ok ("SRLI", [d.toNat, a.toNat, i.toNat])
  | .ADD d a b => .ok ("ADD", [d.toNat, a.toNat, b.toNat])
  | .XOR d a b => .ok ("XOR", [d.toNat, a.toNat, b.toNat])
  | .AND d a b => .ok ("AND", [d.toNat, a.toNat, b.toNat])
  | .SLTU d a b => .ok ("SLTU", [d.toNat, a.toNat, b.toNat])
  | .BNE a b i => .ok ("BNE", [a.toNat, b.toNat, i.toInt])
  | .JAL d i => .ok ("JAL", [d.toNat, i.toInt])
  | .JALR d a i => .ok ("JALR", [d.toNat, a.toNat, i.toInt])
  | _ => .error "unsupported instruction in encoding manifest"

def manifest (program : Program) : Except String String := do
  return (toJson (← program.mapM describe)).compress

end ClAsm.Encoding
