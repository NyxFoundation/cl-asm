import ClAsm.Probes
import ClAsm.Encoding

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

def assembly (name : String) (program : Program) : Except String String := do
  let symbol := name.replace "-" "_"
  let lines ← program.mapM emitInstr
  return ".option norvc\n.option norelax\n.section .text\n.balign 4\n" ++
    s!".globl {symbol}\n.type {symbol}, @function\n{symbol}:\n" ++
    String.join (lines.map (fun line => s!"  {line}\n")) ++
    s!".size {symbol}, . - {symbol}\n"

def linkerScript (name : String) : String :=
  s!"OUTPUT_ARCH(riscv)\nENTRY({name.replace "-" "_"})\n" ++ "PHDRS { text PT_LOAD FLAGS(5); }\n" ++
  "SECTIONS { . = " ++ toString Layout.entry ++ "; .text : { *(.text) } :text }\n"

private def runTool (program : String) (args : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd := program, args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"RISC-V tool failed with exit code {result.exitCode}"

/-- Build the callable probe with an explicit RV64IM/LP64 toolchain. -/
def build (directory : System.FilePath) (name : String) (program : Program) : IO System.FilePath := do
  let text ← IO.ofExcept (assembly name program)
  IO.FS.createDirAll directory
  let source := directory / s!"{name}.s"
  let script := directory / s!"{name}.ld"
  let object := directory / s!"{name}.o"
  let elf := directory / s!"{name}.elf"
  IO.FS.writeFile source text
  IO.FS.writeFile script (linkerScript name)
  IO.FS.writeFile (directory / s!"{name}.program.json") (← IO.ofExcept (Encoding.manifest program))
  let assembler := (← IO.getEnv "RISCV_AS").getD "riscv64-unknown-elf-as"
  let linker := (← IO.getEnv "RISCV_LD").getD "riscv64-unknown-elf-ld"
  runTool assembler #["-march=rv64im", "-mabi=lp64", "-mno-relax", "--fatal-warnings",
    "-o", object.toString, source.toString]
  runTool linker #["-m", "elf64lriscv", "--no-relax", "--fatal-warnings",
    "-T", script.toString, "-o", elf.toString, object.toString]
  return elf

end ClAsm.Codegen
