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

def assembly (name : String) (program : Program) : Except String String := do
  let symbol := symbolName name
  let lines ← program.mapM emitInstr
  return ".option norvc\n.option norelax\n.section .text\n.balign 4\n" ++
    s!".globl {symbol}\n.type {symbol}, @function\n{symbol}:\n" ++
    String.join (lines.map (fun line => s!"  {line}\n")) ++
    s!".size {symbol}, . - {symbol}\n"

end ClAsm.Codegen
