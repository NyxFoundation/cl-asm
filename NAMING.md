# Naming

This project follows the `evm-asm` naming shape with `ClAsm` substituted for
`EvmAsm`.

- Lean modules and files use PascalCase: `ClAsm/Weigh/Program.lean`,
  `ClAsm/Codegen/Driver.lean`.
- Lean namespaces mirror paths: `ClAsm.Weigh`, `ClAsm.Codegen`, and
  `ClAsm.Arithmetic`.
- Lean definitions use lowerCamelCase: `emitInstr`, `linkerScript`,
  `registerInput`, `weighMeaning`, and `build`.
- CLI executable names and generated artifact stems use kebab-case or concise
  lowercase names: `cl-asm`, `cl-asm-test`, `cl-asm-weigh`, `weigh`.
- Codegen follows the evm-asm split: pure instruction/assembly emission lives in
  `ClAsm/Codegen/Emit.lean`, layout/linker-script helpers live in
  `ClAsm/Codegen/Layout.lean`, and IO/toolchain work lives in
  `ClAsm/Codegen/Driver.lean`.
