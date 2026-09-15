import ClAsm.Consensus.WeighJustificationAndFinalization

namespace ClAsm.Codegen.Proofs

def expectedProgramName : String :=
  "weigh_justification_and_finalization"

def expectedWeighComponentNames : List String :=
  [ "copyCheckpoint"
  , "epochAtSlot"
  , "previousEpoch"
  , "hasSupermajority"
  , "blockRootAtEpoch"
  , "shiftJustificationBits"
  , "weighJustificationAndFinalization"
  ]

end ClAsm.Codegen.Proofs
