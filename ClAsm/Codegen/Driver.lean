import ClAsm.Codegen.Layout

namespace ClAsm.Codegen.Driver

def asmPathFor (base : String) : String :=
  base ++ ".s"

def elfPathFor (base : String) : String :=
  base ++ ".elf"

def build (unit : BuildUnit) (halt : HaltConv) (out : Option String) (asmOnly : Bool) : IO UInt32 := do
  let asm := emitBuildUnit unit halt
  match out with
  | none =>
      IO.println asm
      pure 0
  | some base =>
      IO.FS.writeFile (asmPathFor base) asm
      if asmOnly then
        pure 0
      else
        IO.eprintln "ELF linking is not wired yet; rerun with --asm-only."
        pure 1

end ClAsm.Codegen.Driver
