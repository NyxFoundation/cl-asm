# Naming

This project follows the `evm-asm` naming shape with `ClAsm` substituted for
`EvmAsm`.

- Lean modules and files use PascalCase: `ClAsm/Codegen/Layout.lean`,
  `ClAsm/Consensus/WeighJustificationAndFinalization.lean`.
- Lean namespaces mirror paths: `ClAsm.Codegen`, `ClAsm.Consensus`,
  `ClAsm.Rv64`.
- Lean definitions use lowerCamelCase: `emitBuildUnit`, `lookupProgram`,
  `weighJustificationAndFinalization`.
- CLI program names and generated artifact stems use snake_case:
  `weigh_justification_and_finalization`.
- Codegen IO stays in `ClAsm/Codegen/Driver.lean` and
  `ClAsm/Codegen/Cli.lean`; emitter/layout helpers stay pure.
