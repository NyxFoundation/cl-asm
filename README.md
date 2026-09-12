# CL ASM

Lean proofs and RISC-V code for Ethereum consensus-layer operations.
The v0 target is `weigh_justification_and_finalization`; see [DESIGN.md](DESIGN.md).

The helper stage provides proved RV64 instruction sequences for epoch
calculation, genesis-safe previous epoch, justification-bit shifting,
supermajority comparison, block-root addressing, and checkpoint/root copying.
Seven callable ELF probes exercise these helpers and return through `ra`.
The complete `weigh` state contract and branch composition remain the next stage.

## Build and validate

Install [elan](https://github.com/leanprover/elan), Python 3, and GNU RISC-V
binutils. On Debian/Ubuntu the binutils package is
`binutils-riscv64-unknown-elf`. The repository pins Lean 4.33.0 and dependency
revisions in `lean-toolchain` and `lake-manifest.json`.

```sh
lake --no-cache --wfail build
lake env lean scripts/CheckAxioms.lean
.lake/build/bin/cl-asm build
.lake/build/bin/cl-asm-test build
python3 -m unittest discover -s tests -v
```

`RISCV_AS` and `RISCV_LD` select assembler and linker executables when their
names differ from `riscv64-unknown-elf-as` and `riscv64-unknown-elf-ld`.
The generator produces `.s`, `.ld`, `.o`, and `.elf` files under the supplied
output directory. Compression and linker relaxation are disabled; the image
uses RV64IM with LP64 and contains only 4-byte instructions. Each probe has its
own ELF entry point; these test entry points do not change the planned `weigh` ABI.

The tests execute 1,747 deterministic cases, including genesis, all four-bit
patterns, threshold equality and integer limits, root-index wraparound, and
distinct checkpoint contents. They compare independent instruction encodings,
results, every register, complete initialized memory, return, and fuel bounds.
Additional tests reject wrong arithmetic, register corruption, misplaced
stores, traps, infinite execution, altered ELF metadata/bytes, and tool failures.

The Lean proofs cover the modeled instruction sequence. ELF generation,
decoding, loading, and execution-state conversion are checked by tests and are
not formally proved. Details are in [the bootstrap contract](docs/bootstrap.md)
and [helper contracts](docs/helpers.md).
