# Repository Guide

## Scope and architecture
- This is a Lean 4.33.0 project for proving fixed RV64 instruction sequences and validating generated ELF artifacts for Ethereum consensus-layer operations.
- `ClAsm/Weigh/Program.lean` defines the 175-instruction `weigh` program. Its contract, correctness proof, and concrete witness are split across `ClAsm/Weigh/{Contract,Correctness,Witness}.lean` and related modules.
- `ClAsm/Codegen/Emit.lean` is pure instruction-to-assembly emission; `Layout.lean` owns image/linker layout; `Driver.lean` performs IO and invokes the external assembler/linker.
- `Main.lean` generates probe and `weigh` artifacts, `TestMain.lean` validates emission/ELF/helper behavior, and `WeighMain.lean` is the JSON-lines runner used by differential tests.
- Project positioning: this is an independent, forward-looking PoC for the cl-asm concept associated with Justin Drake (JD). It is intended to design and demonstrate cl-asm ahead of that effort; do not imply official affiliation or endorsement.
- Future backend direction: when `leanEthereum/leanVM` supports RISC-V, evaluate replacing the ZisK experiment with leanVM. Keep the current ZisK path until ABI/artifact compatibility, proof boundaries, and benchmark behavior have been compared.

## Required validation order
CI declares this sequence; preserve it because Python tests consume compiled executables and generated files under `build/`:

```sh
lake --no-cache --wfail build
python3 -m venv .venv
.venv/bin/python -m pip install -r tests/requirements.txt
lake env lean scripts/CheckAxioms.lean
.lake/build/bin/cl-asm build
.lake/build/bin/cl-asm-test build
.venv/bin/python -m unittest discover -s tests -v
```

- Required tools are elan, Python 3.12+, and GNU `riscv64-unknown-elf` binutils. `RISCV_AS` and `RISCV_LD` override the assembler and linker names.
- Keep the axiom audit: a successful build without `sorry` is not sufficient validation.
- `.lake/`, `.venv/`, and `build/` are generated and ignored; do not edit their contents as source.

## Proof and artifact boundaries
- Lean proofs cover the modeled instruction sequences, state transition, resource preservation, and bounded return.
- ELF emission, assembly, linking, loading, interpreter conversion, and correspondence to the official Python operation are validated by tests, not formally proved. Do not describe the ELF itself as formally proved.
- Preserve the four independent finalization updates in specification order; later satisfied conditions intentionally take precedence.
- The routine uses an internal ABI and in-place state update. Do not add SSZ decoding, balance aggregation, or zkVM host calls to the proved routine.

## Conventions
- Lean modules/files and namespaces use PascalCase matching their paths; definitions use lowerCamelCase.
- Keep codegen responsibilities in the existing Emit/Layout/Driver split.
- Tests are behavioral: official-reference differential cases, malformed/overflow rejection, ELF mutation rejection, byte/layout checks, and axiom-audit failure cases.
