# CL ASM

Lean proofs and RISC-V code for Ethereum consensus-layer operations.
The v0 target is `weigh_justification_and_finalization`; see [DESIGN.md](DESIGN.md).

The first implementation increment provides the `epochAtSlot` helper and a
callable ELF probe. It loads `slot` through `a0`, computes `slot / 32` in `t0`,
and returns through `ra`. The remaining `weigh` helpers and composition are
not implemented yet.

## Build and validate

Install [elan](https://github.com/leanprover/elan), Python 3, and GNU RISC-V
binutils. On Debian/Ubuntu the binutils package is
`binutils-riscv64-unknown-elf`. The repository pins Lean 4.33.0 and dependency
revisions in `lean-toolchain` and `lake-manifest.json`.

```sh
lake --no-cache --wfail build
lake env lean scripts/CheckAxioms.lean
.lake/build/bin/cl-asm build
.lake/build/bin/cl-asm-test build/epoch-at-slot.elf
python3 -m unittest discover -s tests -v
```

`RISCV_AS` and `RISCV_LD` select assembler and linker executables when their
names differ from `riscv64-unknown-elf-as` and `riscv64-unknown-elf-ld`.
The generator produces `.s`, `.ld`, `.o`, and `.elf` files under the supplied
output directory. Compression and linker relaxation are disabled; the image
uses RV64IM with LP64 and contains three 4-byte instructions.

The tests execute 146 deterministic inputs including zero, epoch boundaries,
the high bit, and the maximum 64-bit slot. They check the quotient, all
registers except `t0`, the complete initialized memory, return, and fuel bounds.
Additional tests reject wrong arithmetic, register corruption, traps, infinite
execution, altered ELF metadata/bytes, and assembler failures.

The Lean proofs cover the modeled instruction sequence. ELF generation,
decoding, loading, and execution-state conversion are checked by tests and are
not formally proved. Details are in [the bootstrap contract](docs/bootstrap.md).
