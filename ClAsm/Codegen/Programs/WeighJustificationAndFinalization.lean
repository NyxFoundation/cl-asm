import ClAsm.Codegen.Layout
import ClAsm.Consensus.WeighJustificationAndFinalization

namespace ClAsm.Codegen.Programs

def weighJustificationAndFinalizationUnit : BuildUnit :=
  { name := "weigh_justification_and_finalization"
    entryLabel := "_start"
    preamble :=
      [ "  # ABI: a0=state, a1=block_roots, a2=total_balance"
      , "  # ABI: a3=previous_balance, a4=current_balance, a5=scratch"
      ]
    program := ClAsm.Consensus.weighJustificationAndFinalization
    dataSection := []
  }

end ClAsm.Codegen.Programs
