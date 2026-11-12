import ClAsm.Aggregate.Harness

namespace ClAsm.Aggregate.Test

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def checkHarness (path : System.FilePath) : IO Unit := do
  let image ← IO.ofExcept (parseElf64 (← IO.FS.readBinFile path))
  let loaded ← IO.ofExcept (Harness.validateImage image)
  let input : ClAsm.Aggregate.Input := ⟨96, [⟨32000000000, 0, BitVec.allOnes 64, 0⟩], [2], [2]⟩
  let initial := Harness.prepare loaded input
  let result ← IO.ofExcept (Harness.runCase loaded input)
  check (result.total == 32000000000 && result.steps == 76) "aggregate result or steps"
  let (final, _) ← IO.ofExcept (Harness.execute (stepBound 1) initial)
  let changedReg := { final with regs := final.regs.set! 14 0 }
  let changedInput := { final with mem := final.mem.insert (BitVec.ofNat 64 validatorsAddress) 1 }
  let grownMemory := { final with mem := final.mem.insert (BitVec.ofNat 64 (scratchAddress + 32)) 1 }
  let changedHost := { final with inputBufBase := final.inputBufBase + 8 }
  let changedCode := { final with code := final.code.insert (BitVec.ofNat 64 entry) (.JAL .x0 0) }
  for corrupted in [changedReg, changedInput, grownMemory, changedHost, changedCode] do
    check ((Harness.checkPreservation initial corrupted).toOption.isNone)
      "aggregate preservation check accepted corruption"
  let infinite := { initial with code := initial.code.insert (BitVec.ofNat 64 entry) (.JAL .x0 0) }
  let trapped := { initial with code := initial.code.insert (BitVec.ofNat 64 entry) (.LD .x5 .x10 1) }
  check ((Harness.execute 76 infinite).toOption.isNone) "aggregate infinite loop accepted"
  check ((Harness.execute 76 trapped).toOption.isNone) "aggregate unaligned access accepted"

end ClAsm.Aggregate.Test
