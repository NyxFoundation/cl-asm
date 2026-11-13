import ClAsm.Rv64
import LeanAsm.Rv64.Emit

namespace ClAsm.Codegen

open RiscvZkvm.Rv64

/-- Only fixed-width instructions accepted by LeanAsm are emitted;
    pseudoinstructions cannot silently change proved program size. -/
def emitInstr (instruction : Instr) : Except String String := do
  return LeanAsm.Rv64.emitInstr (← ClAsm.Rv64.Upstream.instr instruction)

def symbolName (name : String) : String :=
  name.replace "-" "_"

def assembly (name : String) (program : Program) : Except String String :=
  LeanAsm.emitAsm (symbolName name) program

end ClAsm.Codegen
