import ClAsm.Aggregate.Harness

namespace ClAsm.Aggregate.Benchmark

open Lean RiscvZkvm.Rv64 RiscvZkvm.Interpreter

structure Report where
  result : Input.Result
  iterationsPerBatch : Nat
  batchNanoseconds : List Nat
  checksum : Nat
  deriving ToJson

private def batch (initial : ExecState) (bound iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for i in [0:iterations] do
    let next := { initial with regs := initial.regs.set! 5 (BitVec.ofNat 64 i) }
    let (final, steps) ← IO.ofExcept (Harness.execute bound next)
    checksum := checksum + steps + (Harness.readSums final).1.toNat
  return checksum

/-- Timing excludes ELF loading, input preparation, JSON, and preservation checks. -/
def measure (loaded : Loaded) (input : Aggregate.Input) (iterations batches : Nat) : IO Report := do
  unless 0 < iterations && iterations ≤ 100000 && 0 < batches && batches ≤ 1000 do
    throw <| IO.userError "invalid benchmark iteration or batch count"
  let result ← IO.ofExcept (Harness.runCase loaded input)
  let initial := Harness.prepare loaded input
  let bound := stepBound input.validators.length
  let _ ← batch initial bound 1
  let mut times := []
  let mut checksum := 0
  for _ in [0:batches] do
    let start ← IO.monoNanosNow
    let value ← batch initial bound iterations
    let stop ← IO.monoNanosNow
    times := (stop - start) :: times
    checksum := checksum + value
  unless checksum == batches * iterations * (result.steps + result.total) do
    throw <| IO.userError "benchmark checksum mismatch"
  return ⟨result, iterations, times.reverse, checksum⟩

end ClAsm.Aggregate.Benchmark
