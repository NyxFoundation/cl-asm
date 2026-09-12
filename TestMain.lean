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
  check (Codegen.emitInstr .ECALL |>.toOption.isNone) "unsupported instructions must fail"

private def shouldRejectBadExecution (path : System.FilePath) : IO Unit := do
  let image ← IO.ofExcept (RiscvZkvm.Interpreter.parseElf64 (← IO.FS.readBinFile path))
  let loaded ← IO.ofExcept (Harness.validateImage image)
  let entry := BitVec.ofNat 64 Layout.entry
  let alter (offset : Nat) (instruction : Instr) :=
    { loaded with state := { loaded.state with
      code := loaded.state.code.insert (entry + BitVec.ofNat 64 offset) instruction } }
  let fails (result : Except String Unit) (expected : String) :=
    match result with
    | .error message => message == expected
    | .ok _ => false
  check (fails (Harness.checkCase (alter 4 (.SRLI .x5 .x5 6)) 64) "epoch result mismatch")
    "wrong arithmetic was accepted"
  check (fails (Harness.checkCase (alter 8 (.JAL .x0 0)) 64)
    "routine did not return within the step bound") "non-returning code was accepted"
  check (fails (Harness.checkCase (alter 0 (.LD .x5 .x10 1)) 64)
    "routine trapped before returning") "unaligned load was accepted"
  let clobber := { loaded with state := { loaded.state with
    code := loaded.state.code.insert entry (.LD .x6 .x10 0)
      |>.insert (entry + 4) (.SRLI .x5 .x6 5) } }
  check (fails (Harness.checkCase clobber 64) "preserved register changed")
    "register corruption was accepted"

def main (args : List String) : IO UInt32 := do
  try
    shouldEmitExactInstructionForms
    match args with
    | [path] =>
      Harness.checkElf path
      shouldRejectBadExecution path
    | _ => throw <| IO.userError "usage: cl-asm-test <epoch-at-slot.elf>"
    IO.println "PASS: assembly emission, ELF layout, epoch results, preservation, and return"
    return 0
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1
