import ClAsm.Codegen.Driver
import ClAsm.Codegen.Programs

namespace ClAsm.Codegen.Cli

structure Options where
  program : String
  halt : HaltConv
  out : Option String
  asmOnly : Bool
  listPrograms : Bool
  help : Bool
deriving Repr

def defaultOptions : Options :=
  { program := "weigh_justification_and_finalization"
    halt := .sp1
    out := none
    asmOnly := false
    listPrograms := false
    help := false
  }

private def usage : String :=
  "usage: lake exe codegen -- [OPTIONS]\n" ++
  "\n" ++
  "Options:\n" ++
  "  --program NAME       Build a named program\n" ++
  "  --list-programs      Print available program names\n" ++
  "  --halt sp1|linux93   Select the halt convention\n" ++
  "  -o PATH              Write PATH.s instead of printing assembly\n" ++
  "  --asm-only           Stop after emitting assembly\n" ++
  "  -h, --help           Show this help"

private def parseHalt (value : String) : Except String HaltConv :=
  match HaltConv.parse value with
  | some halt => .ok halt
  | none => .error ("unknown halt convention: " ++ value)

partial def parseArgs (args : List String) (opts : Options) : Except String Options :=
  match args with
  | [] => .ok opts
  | "--program" :: name :: rest => parseArgs rest { opts with program := name }
  | "--list-programs" :: rest => parseArgs rest { opts with listPrograms := true }
  | "--halt" :: value :: rest =>
      match parseHalt value with
      | .ok halt => parseArgs rest { opts with halt := halt }
      | .error msg => .error msg
  | "-o" :: path :: rest => parseArgs rest { opts with out := some path }
  | "--out" :: path :: rest => parseArgs rest { opts with out := some path }
  | "--asm-only" :: rest => parseArgs rest { opts with asmOnly := true }
  | "-h" :: rest => parseArgs rest { opts with help := true }
  | "--help" :: rest => parseArgs rest { opts with help := true }
  | flag :: _ => .error ("unknown or incomplete argument: " ++ flag)

def main (args : List String) : IO UInt32 := do
  match parseArgs args defaultOptions with
  | .error msg =>
      IO.eprintln msg
      IO.eprintln usage
      pure 1
  | .ok opts =>
      if opts.help then
        IO.println usage
        pure 0
      else if opts.listPrograms then
        for name in knownProgramNames do
          IO.println name
        pure 0
      else
        match lookupProgram opts.program with
        | none =>
            IO.eprintln ("unknown program: " ++ opts.program)
            IO.eprintln "Run with --list-programs to see available programs."
            pure 1
        | some unit =>
            Driver.build unit opts.halt opts.out opts.asmOnly

end ClAsm.Codegen.Cli
