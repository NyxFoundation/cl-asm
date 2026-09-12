import ClAsm.EpochAtSlot

namespace ClAsm.Codegen

open RiscvZkvm.Rv64

/-- Only supported real instructions are emitted; pseudoinstructions cannot
    silently change the size or meaning of the proved Program. -/
def emitInstr : Instr → Except String String
  | .LD dst src offset => .ok s!"ld x{dst.toNat}, {offset.toInt}(x{src.toNat})"
  | .SRLI dst src shift => .ok s!"srli x{dst.toNat}, x{src.toNat}, {shift.toNat}"
  | .JALR dst src offset => .ok s!"jalr x{dst.toNat}, {offset.toInt}(x{src.toNat})"
  | _ => .error "unsupported RISC-V instruction"

def assembly (program : Program) : Except String String := do
  let lines ← program.mapM emitInstr
  return ".option norvc\n.option norelax\n.section .text\n.balign 4\n" ++
    ".globl epoch_at_slot\n.type epoch_at_slot, @function\nepoch_at_slot:\n" ++
    String.join (lines.map (fun line => s!"  {line}\n")) ++
    ".size epoch_at_slot, . - epoch_at_slot\n"

def linkerScript : String :=
  "OUTPUT_ARCH(riscv)\nENTRY(epoch_at_slot)\nPHDRS { text PT_LOAD FLAGS(5); }\n" ++
  "SECTIONS { . = " ++ toString Layout.entry ++ "; .text : { *(.text) } :text }\n"

private def runTool (program : String) (args : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd := program, args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"RISC-V tool failed with exit code {result.exitCode}"

/-- Build the callable probe with an explicit RV64IM/LP64 toolchain. -/
def build (directory : System.FilePath) : IO System.FilePath := do
  let text ← IO.ofExcept (assembly EpochAtSlot.callable)
  IO.FS.createDirAll directory
  let source := directory / "epoch-at-slot.s"
  let script := directory / "epoch-at-slot.ld"
  let object := directory / "epoch-at-slot.o"
  let elf := directory / "epoch-at-slot.elf"
  IO.FS.writeFile source text
  IO.FS.writeFile script linkerScript
  let assembler := (← IO.getEnv "RISCV_AS").getD "riscv64-unknown-elf-as"
  let linker := (← IO.getEnv "RISCV_LD").getD "riscv64-unknown-elf-ld"
  runTool assembler #["-march=rv64im", "-mabi=lp64", "-mno-relax", "--fatal-warnings",
    "-o", object.toString, source.toString]
  runTool linker #["-m", "elf64lriscv", "--no-relax", "--fatal-warnings",
    "-T", script.toString, "-o", elf.toString, object.toString]
  return elf

end ClAsm.Codegen
