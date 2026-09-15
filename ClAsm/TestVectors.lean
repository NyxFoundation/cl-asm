import ClAsm.Probes

namespace ClAsm.TestVectors

open RiscvZkvm.Rv64

structure Vector where
  inputs : List (Reg × Word) := []
  memory : List (Word × Word) := []
  outputs : List (Reg × Word)
  writes : List (Word × Word) := []

def word := BitVec.ofNat 64

def samples : List Nat :=
  [0, 1, 31, 32, 33, 63, 64, 65, 255, 256, 257, 8191, 8192, 8193,
    2^32 - 1, 2^32, 2^63 - 1, 2^63, 2^64 - 33, 2^64 - 32, 2^64 - 1] ++
  (List.range 128).map (fun i => (i * 0x9e3779b97f4a7c15 + 17) % 2^64)

def epochVector (slot : Nat) : Vector :=
  { memory := [(word Layout.stateAddress, word slot)], outputs := [(.x5, word (slot / 32))] }

private def thresholdInputs : List (Nat × Nat) :=
  let totals := [0, 1, 2, 3, 96, 2^32 - 1, 2^32, 2^62, 2^63 - 2, 2^63 - 1]
  let boundaries := totals.flatMap fun total =>
    [0, 1, (2 * total) / 3 - 1, (2 * total) / 3, (2 * total) / 3 + 1,
      (2^64 - 1) / 3].map fun vote => (vote, total)
  let sampled := (List.range 256).map fun i =>
    ((i * 0x9e3779b97f4a7c15 + 7) % ((2^64 - 1) / 3 + 1),
      (i * 0x517cc1b727220a95 + 3) % 2^63)
  (boundaries ++ sampled).filter fun (vote, total) => 3 * vote < 2^64 && 2 * total < 2^64

private def copyVector (rootOnly : Bool) (index : Nat) : Vector := Id.run do
  let count := if rootOnly then 4 else 5
  let source := if rootOnly then Layout.rootsAddress + (index % 256) * 1024
    else Layout.stateAddress + 56
  let target := if index % 2 == 0 then Layout.scratchAddress + 16
    else Layout.stateAddress + (if rootOnly then 24 else 16)
  let values := (List.range count).map fun i =>
    word ((index * 0x0102030405060708 + i * 0xfedcba9876543211) % 2^64)
  return {
    inputs := [(.x10, word source), (.x11, word target)]
    memory := values.zipIdx.map (fun (v, i) => (word (source + 8 * i), v))
    outputs := [(.x5, values[count - 1]!)]
    writes := values.zipIdx.map (fun (v, i) => (word (target + 8 * i), v)) }

/-- Expected values use unbounded integer arithmetic, independently of the RV64 helpers. -/
def forKind : Probes.Kind → List Vector
  | .epochAtSlot => samples.map epochVector
  | .previousEpoch => samples.map fun epoch =>
      { inputs := [(.x10, word epoch)], outputs := [(.x5, word (epoch - 1))] }
  | .shiftBits => (List.range 32 ++ samples).map fun bits =>
      { inputs := [(.x5, word bits)], outputs := [(.x5, word ((bits * 2) % 16))] }
  | .supermajority => thresholdInputs.map fun (vote, total) =>
      { inputs := [(.x10, word vote), (.x11, word total)],
        outputs := [(.x5, if 3 * vote ≥ 2 * total then 1 else 0), (.x6, word (2 * total))] }
  | .rootAddress => (List.range 513 ++ samples).map fun epoch =>
      { inputs := [(.x10, word epoch)],
        outputs := [(.x5, word (Layout.rootsAddress + ((epoch * 32) % 8192) * 32))] }
  | .checkpointCopy => (List.range 32).map (copyVector false)
  | .rootCopy => (List.range 258).map (copyVector true)

end ClAsm.TestVectors
