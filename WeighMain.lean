import ClAsm.Weigh.Benchmark

open Lean ClAsm.Weigh

def main (args : List String) : IO UInt32 := do
  try
    let (path, benchmark) ← match args with
      | [path] => pure (path, none)
      | [path, "--benchmark", iterations, batches] => do
        let some n := iterations.toNat? | throw <| IO.userError "invalid iteration count"
        let some b := batches.toNat? | throw <| IO.userError "invalid batch count"
        pure (path, some (n, b))
      | _ => throw <| IO.userError "usage: cl-asm-weigh <weigh.elf> [--benchmark <iterations> <batches>]"
    let image ← IO.ofExcept (RiscvZkvm.Interpreter.parseElf64 (← IO.FS.readBinFile path))
    let loaded ← IO.ofExcept (Harness.validateImage image)
    let input ← IO.getStdin
    let output ← IO.getStdout
    repeat
      let line ← input.getLine
      if line.isEmpty then break
      let data : Input.Data ← IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse line)))
      let inputCase ← IO.ofExcept data.decode
      let result ← match benchmark with
        | none => pure (toJson (← IO.ofExcept (Harness.runCase loaded inputCase)))
        | some (n, b) => pure (toJson (← Benchmark.measure loaded inputCase n b))
      output.putStrLn result.compress
    return 0
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1
