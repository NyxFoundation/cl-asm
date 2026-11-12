import ClAsm.Aggregate.Benchmark

open Lean ClAsm.Aggregate

private def usage : String :=
  "usage: cl-asm-aggregate <aggregate.elf> [--benchmark <iterations> <batches>]"

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] then
    IO.println usage
    return 0
  try
    let (path, benchmark) ← match args with
      | [path] => pure (path, none)
      | [path, "--benchmark", iterations, batches] => do
        let some n := iterations.toNat? | throw <| IO.userError usage
        let some b := batches.toNat? | throw <| IO.userError usage
        pure (path, some (n, b))
      | _ => throw <| IO.userError usage
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
  catch _ =>
    IO.eprintln "FAIL: aggregate input, image, arguments, or execution rejected"
    IO.eprintln usage
    return 1
