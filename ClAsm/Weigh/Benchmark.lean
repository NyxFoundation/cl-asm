import ClAsm.Weigh.Harness

namespace ClAsm.Weigh.Benchmark

open Lean RiscvZkvm.Rv64 RiscvZkvm.Interpreter

structure Report where
  result : Input.Result
  iterationsPerBatch : Nat
  batchNanoseconds : List Nat
  checksum : Nat
  deriving ToJson

/-- Vary an overwritten temporary to keep each pure interpreter call dependent
    on its iteration. The checksum makes its returned values observable. -/
private def batch (initial : ExecState) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for i in [0:iterations] do
    let next := { initial with regs := initial.regs.set! 5 (BitVec.ofNat 64 i) }
    let (final, steps) ← IO.ofExcept (Harness.execute stepBound next)
    checksum := checksum + steps + (final.mem[BitVec.ofNat 64 (Layout.stateAddress + 8)]?.getD 0).toNat
  return checksum

/-- Timed batches exclude ELF loading, state/root preparation, JSON, and full
    preservation checks. Times include interpreter calls, register reset, and checksum. -/
def measure (loaded : Loaded) (input : Input.Case) (iterations batches : Nat) : IO Report := do
  unless 0 < iterations && iterations ≤ 100000 && 0 < batches && batches ≤ 1000 do
    throw <| IO.userError "invalid benchmark iteration or batch count"
  let result ← IO.ofExcept (Harness.runCase loaded input)
  let initial := Harness.prepare loaded input
  let _ ← batch initial 100
  let mut times := []
  let mut checksum := 0
  for _ in [0:batches] do
    let start ← IO.monoNanosNow
    let value ← batch initial iterations
    let stop ← IO.monoNanosNow
    times := (stop - start) :: times
    checksum := checksum + value
  unless checksum == batches * iterations * (result.steps + result.bits) do
    throw <| IO.userError "benchmark checksum mismatch"
  return ⟨result, iterations, times.reverse, checksum⟩

end ClAsm.Weigh.Benchmark
