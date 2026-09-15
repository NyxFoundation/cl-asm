import ClAsm.Codegen.Layout
import ClAsm.Codegen.Programs.WeighJustificationAndFinalization

namespace ClAsm.Codegen

def knownPrograms : List BuildUnit :=
  [ Programs.weighJustificationAndFinalizationUnit ]

def knownProgramNames : List String :=
  knownPrograms.map (fun unit => unit.name)

def lookupProgram (name : String) : Option BuildUnit :=
  knownPrograms.find? (fun unit => unit.name == name)

end ClAsm.Codegen
