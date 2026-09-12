import ClAsm.Probes

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
  | .ADD dst src1 src2 => .ok s!"add x{dst.toNat}, x{src1.toNat}, x{src2.toNat}"
  | .SLTU dst src1 src2 => .ok s!"sltu x{dst.toNat}, x{src1.toNat}, x{src2.toNat}"
  | .JALR dst src offset => .ok s!"jalr x{dst.toNat}, {offset.toInt}(x{src.toNat})"
  | _ => .error "unsupported RISC-V instruction"

def assembly (kind : Probes.Kind) : Except String String := do
  let lines ← kind.program.mapM emitInstr
  return ".option norvc\n.option norelax\n.section .text\n.balign 4\n" ++
    s!".globl {kind.symbol}\n.type {kind.symbol}, @function\n{kind.symbol}:\n" ++
    String.join (lines.map (fun line => s!"  {line}\n")) ++
    s!".size {kind.symbol}, . - {kind.symbol}\n"

def linkerScript (kind : Probes.Kind) : String :=
  s!"OUTPUT_ARCH(riscv)\nENTRY({kind.symbol})\n" ++ "PHDRS { text PT_LOAD FLAGS(5); }\n" ++
  "SECTIONS { . = " ++ toString Layout.entry ++ "; .text : { *(.text) } :text }\n"

private def runTool (program : String) (args : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd := program, args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"RISC-V tool failed with exit code {result.exitCode}"

/-- Build the callable probe with an explicit RV64IM/LP64 toolchain. -/
def build (directory : System.FilePath) (kind : Probes.Kind) : IO System.FilePath := do
  let text ← IO.ofExcept (assembly kind)
  IO.FS.createDirAll directory
  let source := directory / s!"{kind.name}.s"
  let script := directory / s!"{kind.name}.ld"
  let object := directory / s!"{kind.name}.o"
  let elf := directory / s!"{kind.name}.elf"
  IO.FS.writeFile source text
  IO.FS.writeFile script (linkerScript kind)
  let assembler := (← IO.getEnv "RISCV_AS").getD "riscv64-unknown-elf-as"
  let linker := (← IO.getEnv "RISCV_LD").getD "riscv64-unknown-elf-ld"
  runTool assembler #["-march=rv64im", "-mabi=lp64", "-mno-relax", "--fatal-warnings",
    "-o", object.toString, source.toString]
  runTool linker #["-m", "elf64lriscv", "--no-relax", "--fatal-warnings",
    "-T", script.toString, "-o", elf.toString, object.toString]
  return elf

end ClAsm.Codegen
