import ClAsm.Harness
import ClAsm.Weigh.Program
import ClAsm.Weigh.Input

namespace ClAsm.Weigh.Harness

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def validateImage (image : Elf64Image) : Except String Loaded := do
  require (image.entry == Layout.entry) "ELF entry mismatch"
  require (image.segments.size == 1) "expected one code segment"
  let some segment := image.segments[0]? | throw "missing code segment"
  require (segment.vaddr == Layout.entry) "ELF code address mismatch"
  require (segment.executable && !segment.writable) "ELF code permissions mismatch"
  require (segment.memsz == program.length * 4 && segment.data.size == program.length * 4)
    "ELF code extent mismatch"
  let loaded := load image
  for (instruction, i) in program.zipIdx do
    require (loaded.state.code[BitVec.ofNat 64 (Layout.entry + i * 4)]? == some instruction)
      "decoded instruction differs from weigh Program"
  require (!loaded.state.code.contains (BitVec.ofNat 64 Layout.returnAddress))
    "return address overlaps routine"
  return loaded

def rootWords (root : Root) : List Word := [root.w0, root.w1, root.w2, root.w3]
def checkpointWords (checkpoint : Checkpoint) : List Word := checkpoint.epoch :: rootWords checkpoint.root
def stateWords (state : State) : List Word :=
  [state.slot, state.bits] ++ checkpointWords state.previous ++
    checkpointWords state.current ++ checkpointWords state.finalized

def prepare (loaded : Loaded) (input : Input.Case) : ExecState := Id.run do
  let initial := ClAsm.Harness.prepare loaded
  let regs := initial.regs.set! 12 input.balances.total |>.set! 13 input.balances.previous
    |>.set! 14 input.balances.current
  let mut mem := initial.mem
  for (value, i) in (stateWords input.state).zipIdx do
    mem := mem.insert (BitVec.ofNat 64 (Layout.stateAddress + 8 * i)) value
  for i in [0:Layout.slotsPerHistoricalRoot] do
    for (value, j) in (rootWords (Input.rootAt input.rootSeed i)).zipIdx do
      mem := mem.insert (BitVec.ofNat 64 (Layout.rootsAddress + 32 * i + 8 * j)) value
  return { initial with regs, mem }

def execute : Nat → ExecState → Except String (ExecState × Nat)
  | fuel, state =>
    if state.pc == BitVec.ofNat 64 Layout.returnAddress then .ok (state, 0)
    else match fuel with
      | 0 => .error "weigh did not return within step bound"
      | n + 1 => do
        let some next := state.stepExec | throw "weigh trapped"
        let (final, steps) ← execute n next
        return (final, steps + 1)

private def readCheckpoint (state : ExecState) (base : Nat) : Checkpoint :=
  let read := fun offset => state.mem[BitVec.ofNat 64 (base + offset)]?.getD 0
  ⟨read 0, ⟨read 8, read 16, read 24, read 32⟩⟩

def readState (state : ExecState) : State :=
  ⟨state.mem[BitVec.ofNat 64 Layout.stateAddress]?.getD 0,
    state.mem[BitVec.ofNat 64 (Layout.stateAddress + 8)]?.getD 0,
    readCheckpoint state (Layout.stateAddress + 16), readCheckpoint state (Layout.stateAddress + 56),
    readCheckpoint state (Layout.stateAddress + 96)⟩

def checkPreservation (initial final : ExecState) : Except String Unit := do
  for i in [0:32] do
    if !temporaries.any (fun r => r.toNat == i) then
      require (initial.regs[i]! == final.regs[i]!) "preserved register changed"
  require (initial.mem.size == final.mem.size) "memory footprint changed"
  for (address, value) in initial.mem.toList do
    let a := address.toNat
    let mutableState := Layout.stateAddress + 8 ≤ a && a < Layout.stateAddress + Layout.stateBytes
    let scratch := Layout.scratchAddress ≤ a && a < Layout.scratchAddress + Layout.scratchBytes
    if !mutableState && !scratch then
      require (final.mem[address]? == some value) "preserved memory changed"
  require (final.committed == initial.committed && final.publicValues == initial.publicValues &&
    final.privateInput == initial.privateInput && final.inputBufBase == initial.inputBufBase)
    "host state changed"

def runCase (loaded : Loaded) (input : Input.Case) : Except String Input.Result := do
  let initial := prepare loaded input
  let (final, steps) ← execute stepBound initial
  let actual := readState final
  require (actual == transition input.state input.balances (Input.rootAt input.rootSeed))
    "weigh state differs from mathematical transition"
  require (readCheckpoint final Layout.scratchAddress == input.state.previous &&
    readCheckpoint final (Layout.scratchAddress + 40) == input.state.current)
    "saved checkpoints differ from the original state"
  checkPreservation initial final
  require ((execute (steps - 1) initial).toOption.isNone) "insufficient fuel accepted"
  return Input.result actual steps

end ClAsm.Weigh.Harness
