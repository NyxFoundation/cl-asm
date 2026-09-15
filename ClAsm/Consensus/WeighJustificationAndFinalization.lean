import ClAsm.Consensus.Layout
import ClAsm.Rv64

namespace ClAsm.Consensus

open ClAsm.Rv64

def copyCheckpoint (dst src : Reg) : Program :=
  [ .comment "copyCheckpoint: unroll five 8-byte checkpoint words" ]

def epochAtSlot (dst slotReg scratch : Reg) : Program :=
  [ .comment "epochAtSlot: compute floor(slot / SLOTS_PER_EPOCH)" ]

def previousEpoch (dst epochReg : Reg) : Program :=
  [ .comment "previousEpoch: compute max(epoch - 1, 0)" ]

def hasSupermajority (dst votingBalance totalBalance scratch : Reg) : Program :=
  [ .comment "hasSupermajority: compare 3*votingBalance >= 2*totalBalance" ]

def blockRootAtEpoch (dstRoot stateRootArray epochReg scratch : Reg) : Program :=
  [ .comment "blockRootAtEpoch: read block_roots[(epoch*S) mod N]" ]

def shiftJustificationBits (bitsReg scratch : Reg) : Program :=
  [ .comment "shiftJustificationBits: shift left and keep the low four bits" ]

def saveOldCheckpoints : Program :=
  [ .comment "save old previous/current checkpoints to caller scratch" ]

def computeEpochs : Program :=
  epochAtSlot .t0 .a0 .t1 ++ previousEpoch .t2 .t0

def shiftAndPrepareState : Program :=
  copyCheckpoint .a0 .a0 ++ shiftJustificationBits .t3 .t4

def applyJustificationBranches : Program :=
  hasSupermajority .t5 .a3 .a2 .t6 ++
  blockRootAtEpoch .a5 .a1 .t2 .t6 ++
  hasSupermajority .t5 .a4 .a2 .t6 ++
  blockRootAtEpoch .a5 .a1 .t0 .t6

def applyFinalizationBranches : Program :=
  [ .comment "apply four finalization branches in specification order" ]

def weighJustificationAndFinalization : Program :=
  saveOldCheckpoints ++
  computeEpochs ++
  shiftAndPrepareState ++
  applyJustificationBranches ++
  applyFinalizationBranches ++
  [ .ret ]

end ClAsm.Consensus
