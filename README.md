# cl-asm

Lean/RISC-V scaffolding for the consensus-layer `weigh_justification_and_finalization`
routine.

The repository layout mirrors `evm-asm`:

- `ClAsm/Rv64/` owns the RISC-V instruction vocabulary.
- `ClAsm/Consensus/` owns consensus-layer constants, memory layout, and program
  builders.
- `ClAsm/Codegen/` owns pure assembly emission, build-unit layout, the program
  registry, and the CLI/driver split.
- `ClAsm/Codegen/Programs/` contains one `BuildUnit` per emitted program.
- Generated artifacts belong under `gen-out/`.

The default codegen entry is:

```sh
lake exe codegen -- --program weigh_justification_and_finalization --asm-only
```
