# CL ASM

Lean proofs and RISC-V code for Ethereum consensus-layer operations.
The v0 target is `weigh_justification_and_finalization`; see [DESIGN.md](DESIGN.md).

The complete `weigh` routine has 175 RV64 instructions (700 bytes). Its Lean
contract proves the specified state transition, resource preservation, and
return within 175 steps. Seven additional ELF probes exercise its helpers.
See [the whole-routine contract](docs/weigh.md) for the ABI, admitted inputs,
concrete calling witness, official-reference tests, and trust boundaries.

## Build and validate

Install [elan](https://github.com/leanprover/elan), Python 3.12+, and GNU RISC-V
binutils. On Debian/Ubuntu the binutils package is
`binutils-riscv64-unknown-elf`. The repository pins Lean 4.33.0 and dependency
revisions in `lean-toolchain` and `lake-manifest.json`.

```sh
lake --no-cache --wfail build
python3 -m venv .venv
.venv/bin/python -m pip install -r tests/requirements.txt
lake env lean scripts/CheckAxioms.lean
.lake/build/bin/cl-asm build
.lake/build/bin/cl-asm-test build
.venv/bin/python -m unittest discover -s tests -v
.venv/bin/python scripts/benchmark.py --iterations 200 --batches 21
```

`RISCV_AS` and `RISCV_LD` select assembler and linker executables when their
names differ from `riscv64-unknown-elf-as` and `riscv64-unknown-elf-ld`.
The generator produces `.s`, `.ld`, `.o`, `.elf`, and `.program.json` files under the supplied
output directory. Compression and linker relaxation are disabled; the image
uses RV64IM with LP64 and contains only 4-byte instructions. Each probe has its
own ELF entry point. `weigh.elf` uses the internal ABI from the design.

The tests execute 1,747 helper cases and 4,796 full-routine cases against the
pinned official Python function and its actual SSZ integer types. Coverage
includes genesis, all four-bit patterns, threshold equality and integer limits,
root-index wraparound, and ordered checkpoint overwrites. They check independent
instruction encodings, state results, preserved registers and initialized memory,
return, and fuel bounds.
Additional tests reject wrong arithmetic, register corruption, misplaced
stores, traps, infinite execution, altered ELF metadata/bytes, and tool failures.

The Lean proofs cover the modeled instruction sequence. ELF generation,
decoding, loading, and execution-state conversion are checked by tests and are
not formally proved. Benchmarks report RV64 instruction counts separately from
host interpreter time; they do not measure native RV64 or zkVM proving.
See [the recorded results and reproduction steps](docs/benchmarks.md).
