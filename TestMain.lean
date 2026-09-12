import ClAsm.Codegen
import ClAsm.Harness

open ClAsm RiscvZkvm.Rv64

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def shouldEmitExactInstructionForms : IO Unit := do
  check ((Codegen.emitInstr (.LD .x5 .x10 0)).toOption == some "ld x5, 0(x10)") "LD emission"
  check ((Codegen.emitInstr (.SRLI .x5 .x5 5)).toOption == some "srli x5, x5, 5") "SRLI emission"
  check ((Codegen.emitInstr (.JALR .x0 .x1 0)).toOption == some "jalr x0, 0(x1)") "JALR emission"
  check ((Codegen.emitInstr (.LD .x5 .x10 4095)).toOption == some "ld x5, -1(x10)") "signed offset"
  check ((Codegen.emitInstr (.SRLI .x31 .x30 63)).toOption == some "srli x31, x30, 63") "shift limit"
  check ((Codegen.emitInstr (.SD .x10 .x5 32)).toOption == some "sd x5, 32(x10)") "SD emission"
  check ((Codegen.emitInstr (.SLLI .x5 .x10 1)).toOption == some "slli x5, x10, 1") "SLLI emission"
  check ((Codegen.emitInstr (.SLTIU .x5 .x10 1)).toOption == some "sltiu x5, x10, 1") "SLTIU emission"
  check ((Codegen.emitInstr (.ADDI .x5 .x5 4095)).toOption == some "addi x5, x5, -1") "ADDI emission"
  check ((Codegen.emitInstr (.ANDI .x5 .x5 15)).toOption == some "andi x5, x5, 15") "ANDI emission"
  check ((Codegen.emitInstr (.XORI .x5 .x5 1)).toOption == some "xori x5, x5, 1") "XORI emission"
  check ((Codegen.emitInstr (.ADD .x5 .x10 .x5)).toOption == some "add x5, x10, x5") "ADD emission"
  check ((Codegen.emitInstr (.SLTU .x5 .x5 .x6)).toOption == some "sltu x5, x5, x6") "SLTU emission"
  check (Codegen.emitInstr .ECALL |>.toOption.isNone) "unsupported instructions must fail"

private def shouldRejectBadExecution (path : System.FilePath) : IO Unit := do
  let image ← IO.ofExcept (RiscvZkvm.Interpreter.parseElf64 (← IO.FS.readBinFile path))
  let loaded ← IO.ofExcept (Harness.validateImage .epochAtSlot image)
  let prepared := Harness.prepare loaded
  let entry := BitVec.ofNat 64 Layout.entry
  let alter (offset : Nat) (instruction : Instr) :=
    { prepared with code := prepared.code.insert (entry + BitVec.ofNat 64 offset) instruction }
  let run := fun state => Harness.checkCase .epochAtSlot state (TestVectors.epochVector 64)
  let fails (result : Except String Unit) (expected : String) :=
    match result with
    | .error message => message == expected
    | .ok _ => false
  check (fails (run (alter 4 (.SRLI .x5 .x5 6))) "register result mismatch")
    "wrong arithmetic was accepted"
  check (fails (run (alter 8 (.JAL .x0 0)))
    "routine did not return within the step bound") "non-returning code was accepted"
  check (fails (run (alter 0 (.LD .x5 .x10 1)))
    "routine trapped before returning") "unaligned load was accepted"
  let clobber := { prepared with
    code := prepared.code.insert entry (.LD .x6 .x10 0)
      |>.insert (entry + 4) (.SRLI .x5 .x6 5) }
  check (fails (run clobber) "preserved register changed")
    "register corruption was accepted"

private def shouldRejectCopyCorruption (path : System.FilePath) : IO Unit := do
  let image ← IO.ofExcept (RiscvZkvm.Interpreter.parseElf64 (← IO.FS.readBinFile path))
  let loaded ← IO.ofExcept (Harness.validateImage .checkpointCopy image)
  let prepared := Harness.prepare loaded
  let wrong := { prepared with
    code := prepared.code.insert (BitVec.ofNat 64 (Layout.entry + 4)) (.SD .x11 .x5 40) }
  let some vector := (TestVectors.forKind .checkpointCopy)[1]?
    | throw <| IO.userError "missing copy fixture"
  match Harness.checkCase .checkpointCopy wrong vector with
  | .error message => check (message == "memory result or preservation mismatch") "wrong failure"
  | .ok _ => throw <| IO.userError "out-of-region store was accepted"

def main (args : List String) : IO UInt32 := do
  try
    shouldEmitExactInstructionForms
    match args with
    | [directory] =>
      for kind in Probes.all do
        Harness.checkElf kind (System.FilePath.mk directory / s!"{kind.name}.elf")
      shouldRejectBadExecution (System.FilePath.mk directory / "epoch-at-slot.elf")
      shouldRejectCopyCorruption (System.FilePath.mk directory / "copy-checkpoint.elf")
    | [name, path] =>
      let some kind := Probes.all.find? (fun kind => kind.name == name)
        | throw <| IO.userError "unknown probe"
      Harness.checkElf kind path
    | _ => throw <| IO.userError "usage: cl-asm-test <directory> | <probe-name> <probe.elf>"
    IO.println "PASS: assembly emission, ELF layout, helper results, preservation, and return"
    return 0
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1
