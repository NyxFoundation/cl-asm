import RiscvZkvm.Rv64.Program

namespace ClAsm.Codegen

open RiscvZkvm.Rv64

/-- Only supported real instructions are emitted; pseudoinstructions cannot
    silently change the size or meaning of the proved Program. -/
def emitInstr : Instr → Except String String
  | .LD dst src offset => .ok s!"ld x{dst.toNat}, {offset.toInt}(x{src.toNat})"
  | .SD dst src offset => .ok s!"sd x{src.toNat}, {offset.toInt}(x{dst.toNat})"
  | .SRLI dst src shift => .ok s!"srli x{dst.toNat}, x{src.toNat}, {shift.toNat}"
  | .SLLI dst src shift => .ok s!"slli x{dst.toNat}, x{src.toNat}, {shift.toNat}"
  | .SLTIU dst src imm => .ok s!"sltiu x{dst.toNat}, x{src.toNat}, {imm.toInt}"
  | .ADDI dst src imm => .ok s!"addi x{dst.toNat}, x{src.toNat}, {imm.toInt}"
  | .ANDI dst src imm => .ok s!"andi x{dst.toNat}, x{src.toNat}, {imm.toInt}"
  | .XORI dst src imm => .ok s!"xori x{dst.toNat}, x{src.toNat}, {imm.toInt}"
  | .ORI dst src imm => .ok s!"ori x{dst.toNat}, x{src.toNat}, {imm.toInt}"
  | .ADD dst src1 src2 => .ok s!"add x{dst.toNat}, x{src1.toNat}, x{src2.toNat}"
  | .SLTU dst src1 src2 => .ok s!"sltu x{dst.toNat}, x{src1.toNat}, x{src2.toNat}"
  | .XOR dst src1 src2 => .ok s!"xor x{dst.toNat}, x{src1.toNat}, x{src2.toNat}"
  | .AND dst src1 src2 => .ok s!"and x{dst.toNat}, x{src1.toNat}, x{src2.toNat}"
  | .BNE src1 src2 offset => .ok s!"bne x{src1.toNat}, x{src2.toNat}, . + {offset.toInt}"
  | .JAL dst offset => .ok s!"jal x{dst.toNat}, . + {offset.toInt}"
  | .JALR dst src offset => .ok s!"jalr x{dst.toNat}, {offset.toInt}(x{src.toNat})"
  | _ => .error "unsupported RISC-V instruction"

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
