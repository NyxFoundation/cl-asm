import ClAsm.Codegen.Emit

namespace ClAsm.Codegen

open ClAsm.Rv64

inductive HaltConv where
  | sp1
  | linux93
deriving DecidableEq, Repr

def HaltConv.parse : String -> Option HaltConv
  | "sp1" => some .sp1
  | "linux93" => some .linux93
  | _ => none

def memStart : Nat := 0x80000000

def memEnd : Nat := 0x90000000

structure BuildUnit where
  name : String
  entryLabel : String := "_start"
  preamble : List String := []
  program : Program
  postamble : List String := []
  dataSection : List String := []
deriving Repr

def emitDataLabel (name : String) (directives : List String) : List String :=
  (name ++ ":") :: directives.map (fun line => "  " ++ line)

def haltProgram : HaltConv -> Program
  | .sp1 => [ .li .t0 0, .ecall ]
  | .linux93 => [ .li .a7 93, .ecall ]

private def joinLines : List String -> String
  | [] => ""
  | [line] => line
  | line :: rest => line ++ "\n" ++ joinLines rest

def emitBuildUnit (unit : BuildUnit) (halt : HaltConv := .sp1) : String :=
  let textLines :=
    [ ".option norvc"
    , ".section .text"
    , ".global " ++ unit.entryLabel
    , unit.entryLabel ++ ":"
    ] ++ unit.preamble ++
    emitProgramLines unit.program ++
    emitProgramLines (haltProgram halt) ++
    unit.postamble
  let dataLines :=
    match unit.dataSection with
    | [] => []
    | lines => "" :: ".section .data" :: lines
  joinLines (textLines ++ dataLines)

end ClAsm.Codegen
