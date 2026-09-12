import Lean
import ClAsm
import ClAsm.Codegen
import ClAsm.Harness

open Lean in
run_cmd do
  let prefixes := [`ClAsm, `RiscvZkvm.Rv64, `RiscvZkvm.Interpreter]
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut audited : Nat := 0
  let mut observed : List Name := []
  for (name, _) in (← getEnv).constants.toList do
    unless prefixes.any (·.isPrefixOf name) do continue
    audited := audited + 1
    let axioms ← Lean.Elab.Command.liftCoreM (collectAxioms name)
    for axiomName in axioms do
      unless observed.contains axiomName do observed := axiomName :: observed
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  if audited == 0 then throwError "axiom audit found no declarations"
  logInfo m!"Axiom audit passed: {audited} declarations; observed {observed}"
