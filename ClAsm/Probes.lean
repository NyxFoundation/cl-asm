import ClAsm.EpochAtSlot
import ClAsm.Arithmetic
import ClAsm.Checkpoint

namespace ClAsm.Probes

open RiscvZkvm.Rv64

/-- Standalone test entry points; their registers are not a public scalar ABI. -/
inductive Kind where
  | epochAtSlot | previousEpoch | shiftBits | supermajority | rootAddress
  | checkpointCopy | rootCopy
  deriving Repr, BEq, DecidableEq

def all : List Kind :=
  [.epochAtSlot, .previousEpoch, .shiftBits, .supermajority, .rootAddress,
    .checkpointCopy, .rootCopy]

def Kind.name : Kind → String
  | .epochAtSlot => "epoch-at-slot"
  | .previousEpoch => "previous-epoch"
  | .shiftBits => "shift-justification-bits"
  | .supermajority => "has-supermajority"
  | .rootAddress => "block-root-address"
  | .checkpointCopy => "copy-checkpoint"
  | .rootCopy => "copy-root"

def Kind.symbol (kind : Kind) : String := kind.name.replace "-" "_"

def Kind.body : Kind → Program
  | .epochAtSlot => EpochAtSlot.program .x10 .x5
  | .previousEpoch => Arithmetic.previousEpoch .x10 .x5
  | .shiftBits => Arithmetic.shiftJustificationBits .x5
  | .supermajority => Arithmetic.hasSupermajority .x10 .x11 .x5 .x6
  | .rootAddress => Arithmetic.blockRootAddress .x10 .x11 .x5
  | .checkpointCopy => copyCheckpoint .x10 .x11 .x5
  | .rootCopy => copyRoot .x10 .x11 .x5

def Kind.program (kind : Kind) : Program := kind.body ++ [.JALR .x0 .x1 0]

/-- Independent literal RV64 encodings, including RET, kept apart from the emitter. -/
def Kind.encodings : Kind → List UInt32
  | .epochAtSlot => [0x00053283, 0x0052d293, 0x00008067]
  | .previousEpoch => [0x00153293, 0x005502b3, 0xfff28293, 0x00008067]
  | .shiftBits => [0x00129293, 0x00f2f293, 0x00008067]
  | .supermajority => [0x00151293, 0x00a282b3, 0x00159313, 0x0062b2b3, 0x0012c293, 0x00008067]
  | .rootAddress => [0x0ff57293, 0x00a29293, 0x005582b3, 0x00008067]
  | .checkpointCopy => [0x00053283, 0x0055b023, 0x00853283, 0x0055b423,
      0x01053283, 0x0055b823, 0x01853283, 0x0055bc23, 0x02053283, 0x0255b023, 0x00008067]
  | .rootCopy => [0x00053283, 0x0055b023, 0x00853283, 0x0055b423,
      0x01053283, 0x0055b823, 0x01853283, 0x0055bc23, 0x00008067]

def Kind.bytes (kind : Kind) : ByteArray :=
  ⟨(kind.encodings.flatMap fun word => (List.range 4).map fun i =>
    (word >>> (8 * i).toUInt32).toUInt8).toArray⟩

end ClAsm.Probes
