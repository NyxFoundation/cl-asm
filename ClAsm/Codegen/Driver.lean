import ClAsm.Codegen.Layout
import ClAsm.Encoding

namespace ClAsm.Codegen

open RiscvZkvm.Rv64

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
