import ClAsm.EpochAtSlot
import RiscvZkvm.Interpreter.Run

namespace ClAsm.Harness

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

/-- Independent RV64 instruction encodings: LD x5,0(x10); SRLI x5,x5,5; RET. -/
def expectedBytes : ByteArray :=
  ⟨#[0x83, 0x32, 0x05, 0x00, 0x93, 0xd2, 0x52, 0x00, 0x67, 0x80, 0x00, 0x00]⟩

def validateImage (image : Elf64Image) : Except String Loaded := do
  require (image.entry == Layout.entry) "ELF entry mismatch"
  require (image.segments.size == 1) "expected exactly one loadable segment"
  let some segment := image.segments[0]? | throw "missing code segment"
  require (segment.vaddr == Layout.entry) "ELF code address mismatch"
  require (segment.executable && !segment.writable) "ELF code permissions mismatch"
  require (segment.memsz == expectedBytes.size) "ELF code extent mismatch"
  require (segment.data == expectedBytes) "ELF instruction bytes mismatch"
  let loaded := load image
  for (instruction, i) in EpochAtSlot.callable.zipIdx do
    require (loaded.state.code[BitVec.ofNat 64 (Layout.entry + 4 * i)]? == some instruction)
      "decoded instruction differs from the proved Program"
  require (!loaded.state.code.contains (BitVec.ofNat 64 Layout.returnAddress))
    "return address overlaps the routine"
  return loaded

/-- The complete proposed input layout is populated with nonzero sentinel data. -/
def prepare (loaded : Loaded) (slot : Word) : ExecState := Id.run do
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
  mem := mem.insert (BitVec.ofNat 64 Layout.stateAddress) slot
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

def checkCase (loaded : Loaded) (slot : Word) : Except String Unit := do
  let initial := prepare loaded slot
  let final ← runToReturn (BitVec.ofNat 64 Layout.returnAddress) EpochAtSlot.stepBound initial
  require (final.regs[5]!.toNat == slot.toNat / Layout.slotsPerEpoch) "epoch result mismatch"
  for i in [0:32] do
    if i != 5 then require (final.regs[i]! == initial.regs[i]!) "preserved register changed"
  require (final.mem.toList == initial.mem.toList) "memory changed"
  require (final.committed == initial.committed && final.publicValues == initial.publicValues &&
    final.privateInput == initial.privateInput && final.inputBufBase == initial.inputBufBase)
    "host state changed"
  require ((runToReturn (BitVec.ofNat 64 Layout.returnAddress)
    (EpochAtSlot.stepBound - 1) initial).toOption.isNone) "step-bound check accepted insufficient fuel"

def slots : List Nat :=
  [0, 1, 31, 32, 33, 63, 64, 65, 8191, 8192, 8193, 2^32 - 1, 2^32,
    2^63 - 1, 2^63, 2^64 - 33, 2^64 - 32, 2^64 - 1] ++
  (List.range 128).map (fun i => (i * 0x9e3779b97f4a7c15 + 17) % 2^64)

def checkElf (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let image ← IO.ofExcept (parseElf64 bytes)
  let loaded ← IO.ofExcept (validateImage image)
  for slot in slots do IO.ofExcept (checkCase loaded (BitVec.ofNat 64 slot))

end ClAsm.Harness
