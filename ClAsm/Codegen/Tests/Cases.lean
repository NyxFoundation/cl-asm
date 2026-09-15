import ClAsm.Codegen.Programs

namespace ClAsm.Codegen.Tests

structure ProgramTestCase where
  name : String
  programName : String
  asmOnly : Bool := true
deriving Repr

def codegenSmokeCases : List ProgramTestCase :=
  [ { name := "weigh_justification_and_finalization_asm"
      programName := "weigh_justification_and_finalization"
    }
  ]

end ClAsm.Codegen.Tests
