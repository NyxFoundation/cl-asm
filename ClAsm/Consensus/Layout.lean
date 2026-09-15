import ClAsm.Consensus.Constants

namespace ClAsm.Consensus

def slotOffset : Nat := 0

def justificationBitsOffset : Nat := 8

def previousJustifiedCheckpointOffset : Nat := 16

def currentJustifiedCheckpointOffset : Nat := 56

def finalizedCheckpointOffset : Nat := 96

def checkpointEpochOffset : Nat := 0

def checkpointRootOffset : Nat := 8

inductive StateField where
  | slot
  | justificationBits
  | previousJustifiedCheckpoint
  | currentJustifiedCheckpoint
  | finalizedCheckpoint
deriving DecidableEq, Repr

def StateField.offset : StateField -> Nat
  | .slot => slotOffset
  | .justificationBits => justificationBitsOffset
  | .previousJustifiedCheckpoint => previousJustifiedCheckpointOffset
  | .currentJustifiedCheckpoint => currentJustifiedCheckpointOffset
  | .finalizedCheckpoint => finalizedCheckpointOffset

end ClAsm.Consensus
