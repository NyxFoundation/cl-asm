import ClAsm.TestVectors
import RiscvZkvm.Interpreter.Run

namespace ClAsm.Harness

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def validateImage (kind : Probes.Kind) (image : Elf64Image) : Except String Loaded := do
  require (image.entry == Layout.entry) "ELF entry mismatch"
  require (image.segments.size == 1) "expected exactly one loadable segment"
  let some segment := image.segments[0]? | throw "missing code segment"
  require (segment.vaddr == Layout.entry) "ELF code address mismatch"
  require (segment.executable && !segment.writable) "ELF code permissions mismatch"
  require (segment.memsz == kind.bytes.size) "ELF code extent mismatch"
  require (segment.data == kind.bytes) "ELF instruction bytes mismatch"
  let loaded := load image
  for (instruction, i) in kind.program.zipIdx do
    require (loaded.state.code[BitVec.ofNat 64 (Layout.entry + 4 * i)]? == some instruction)
      "decoded instruction differs from the proved Program"
  require (!loaded.state.code.contains (BitVec.ofNat 64 Layout.returnAddress))
    "return address overlaps the routine"
  return loaded

/-- The complete proposed input layout is populated with nonzero sentinel data. -/
def prepare (loaded : Loaded) : ExecState := Id.run do
  let regs := (List.range 32).toArray.map (fun i => BitVec.ofNat 64 (0x1000 + i * 8))
  let regs := regs.set! 0 0 |>.set! 1 (BitVec.ofNat 64 Layout.returnAddress)
    |>.set! 10 (BitVec.ofNat 64 Layout.stateAddress)
    |>.set! 11 (BitVec.ofNat 64 Layout.rootsAddress)
    |>.set! 12 96 |>.set! 13 64 |>.set! 14 64
    |>.set! 15 (BitVec.ofNat 64 Layout.scratchAddress)
  let regions := [(Layout.stateAddress, Layout.stateBytes),
    (Layout.rootsAddress, Layout.rootsBytes), (Layout.scratchAddress, Layout.scratchBytes)]
  let mut mem := loaded.state.mem
  for (base, bytes) in regions do
    for i in [0:bytes / 8] do
      mem := mem.insert (BitVec.ofNat 64 (base + 8 * i)) (BitVec.ofNat 64 (base + 8 * i + 7))
  return { loaded.state with regs, mem }

/-- Stop before fetching the caller's return address. No ECALL or host ABI is used. -/
def runToReturn (returnPC : Word) : Nat → ExecState → Except String ExecState
  | fuel, state =>
    if state.pc == returnPC then .ok state
    else match fuel with
      | 0 => .error "routine did not return within the step bound"
      | remaining + 1 => do
        let some next := state.stepExec | throw "routine trapped before returning"
        runToReturn returnPC remaining next

def checkCase (kind : Probes.Kind) (prepared : ExecState) (vector : TestVectors.Vector) :
    Except String Unit := do
  let initial := { prepared with
    regs := vector.inputs.foldl (fun regs (r, v) => regs.set! r.toNat v) prepared.regs,
    mem := vector.memory.foldl (fun mem (a, v) => mem.insert a v) prepared.mem }
  let final ← runToReturn (BitVec.ofNat 64 Layout.returnAddress) kind.program.length initial
  for (reg, value) in vector.outputs do
    require (final.regs[reg.toNat]! == value) "register result mismatch"
  for i in [0:32] do
    if !vector.outputs.any (fun (reg, _) => reg.toNat == i) then
      require (final.regs[i]! == initial.regs[i]!) "preserved register changed"
  let expectedMemory := vector.writes.foldl (fun mem (a, v) => mem.insert a v) initial.mem
  require (final.mem.toList == expectedMemory.toList) "memory result or preservation mismatch"
  require (final.committed == initial.committed && final.publicValues == initial.publicValues &&
    final.privateInput == initial.privateInput && final.inputBufBase == initial.inputBufBase)
    "host state changed"
  require ((runToReturn (BitVec.ofNat 64 Layout.returnAddress)
    (kind.program.length - 1) initial).toOption.isNone) "step-bound check accepted insufficient fuel"

def checkElf (kind : Probes.Kind) (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let image ← IO.ofExcept (parseElf64 bytes)
  let loaded ← IO.ofExcept (validateImage kind image)
  let prepared := prepare loaded
  let vectors := TestVectors.forKind kind
  for vector in vectors do IO.ofExcept (checkCase kind prepared vector)
  IO.println s!"{kind.name}: {vectors.length} cases"

end ClAsm.Harness
