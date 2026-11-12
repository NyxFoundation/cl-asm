import ClAsm.Aggregate.Input
import RiscvZkvm.Interpreter.Run

namespace ClAsm.Aggregate.Harness

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def validateImage (image : Elf64Image) : Except String Loaded := do
  require (image.entry == entry) "ELF entry mismatch"
  require (image.segments.size == 1) "expected one code segment"
  let some segment := image.segments[0]? | throw "missing code segment"
  require (segment.vaddr == entry) "ELF code address mismatch"
  require (segment.executable && !segment.writable) "ELF code permissions mismatch"
  require (segment.memsz == program.length * 4 && segment.data.size == program.length * 4)
    "ELF code extent mismatch"
  let loaded := load image
  for (instruction, i) in program.zipIdx do
    require (loaded.state.code[BitVec.ofNat 64 (entry + i * 4)]? == some instruction)
      "decoded instruction differs from aggregate Program"
  require (!loaded.state.code.contains (BitVec.ofNat 64 returnAddress))
    "return address overlaps routine"
  return loaded

def prepare (loaded : Loaded) (input : Aggregate.Input) : ExecState := Id.run do
  let regs := (List.range 32).toArray.map (fun i => BitVec.ofNat 64 (0x1000 + i * 8))
  let regs := regs.set! 0 0 |>.set! 1 (BitVec.ofNat 64 returnAddress)
    |>.set! 10 (BitVec.ofNat 64 validatorsAddress)
    |>.set! 11 (BitVec.ofNat 64 previousFlagsAddress)
    |>.set! 12 (BitVec.ofNat 64 currentFlagsAddress)
    |>.set! 13 (BitVec.ofNat 64 input.validators.length) |>.set! 14 input.slot
    |>.set! 15 (BitVec.ofNat 64 scratchAddress)
  let mut mem := loaded.state.mem
  for (v, i) in input.validators.zipIdx do
    for (value, j) in [v.effectiveBalance, v.activationEpoch, v.exitEpoch, v.slashed].zipIdx do
      mem := mem.insert (BitVec.ofNat 64 (validatorsAddress + 32 * i + 8 * j)) value
  for (base, flags) in [(previousFlagsAddress, input.previousFlags),
      (currentFlagsAddress, input.currentFlags)] do
    for (value, i) in flags.zipIdx do
      mem := mem.insert (BitVec.ofNat 64 (base + 8 * i)) value
  for offset in [0, 8, 16] do
    mem := mem.insert (BitVec.ofNat 64 (scratchAddress + offset)) (BitVec.ofNat 64 (0xa5 + offset))
  for address in [validatorsAddress - 8, previousFlagsAddress - 8, currentFlagsAddress - 8,
      scratchAddress - 8, scratchAddress + answerBytes] do
    if !mem.contains (BitVec.ofNat 64 address) then
      mem := mem.insert (BitVec.ofNat 64 address) 0xdeadbeef
  return { loaded.state with regs, mem }

private def executeLoop : Nat → Nat → ExecState → Except String (ExecState × Nat)
  | fuel, steps, state =>
    if state.pc == BitVec.ofNat 64 returnAddress then .ok (state, steps)
    else match fuel with
      | 0 => .error "aggregate did not return within step bound"
      | n + 1 => match state.stepExec with
        | none => .error "aggregate trapped"
        | some next => executeLoop n (steps + 1) next

def execute (fuel : Nat) (state : ExecState) : Except String (ExecState × Nat) :=
  executeLoop fuel 0 state

def readSums (state : ExecState) : Word × Word × Word :=
  (state.mem[BitVec.ofNat 64 scratchAddress]?.getD 0,
    state.mem[BitVec.ofNat 64 (scratchAddress + 8)]?.getD 0,
    state.mem[BitVec.ofNat 64 (scratchAddress + 16)]?.getD 0)

def checkPreservation (initial final : ExecState) : Except String Unit := do
  for i in [0:32] do
    if !temporaries.any (fun r => r.toNat == i) then
      require (initial.regs[i]! == final.regs[i]!) "preserved register changed"
  require (initial.mem.size == final.mem.size) "memory footprint changed"
  for (address, value) in initial.mem.toList do
    if !(scratchAddress ≤ address.toNat && address.toNat < scratchAddress + answerBytes) then
      require (final.mem[address]? == some value) "preserved memory changed"
  require (initial.code == final.code) "code changed"
  require (final.committed == initial.committed && final.publicValues == initial.publicValues &&
    final.privateInput == initial.privateInput && final.inputBufBase == initial.inputBufBase)
    "host state changed"

def runCase (loaded : Loaded) (input : Aggregate.Input) : Except String Input.Result := do
  let initial := prepare loaded input
  let (final, steps) ← execute (stepBound input.validators.length) initial
  let actual := readSums final
  require (actual == aggregateResult input) "aggregate result differs from mathematical sums"
  checkPreservation initial final
  require ((execute (steps - 1) initial).toOption.isNone) "insufficient fuel accepted"
  return Input.result actual steps

end ClAsm.Aggregate.Harness
