import ClAsm.Probes
import ClAsm.Codegen
import ClAsm.Weigh.Program

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [directory] =>
      for kind in ClAsm.Probes.all do
        let path ← ClAsm.Codegen.build directory kind.name kind.program
        IO.println s!"Generated {path}"
      let path ← ClAsm.Codegen.build directory "weigh" ClAsm.Weigh.program
      IO.println s!"Generated {path}"
      return 0
    | _ =>
      IO.eprintln "usage: cl-asm <output-directory>"
      return 1
  catch _ =>
    IO.eprintln "ELF generation failed; check the output directory and RISCV_AS/RISCV_LD tools"
    return 1
