# CL ASM

Lean proofs and RISC-V code for Ethereum consensus-layer operations.
The v0 target is `weigh_justification_and_finalization`; see [DESIGN.md](DESIGN.md)
for the design and [the roadmap](docs/roadmap.md) for the purpose, the zkVM
findings, and what remains to be proved.

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

## ZisK guest

`guest/zisk` wraps the checked `weigh.elf` for the [ZisK](https://github.com/0xPolygonHermez/zisk)
zkVM. The wrapper reads the 136-byte state, three balances, and a root seed as
input, materializes all 8192 roots as the spec's in-memory `block_roots`, calls
`weigh`, and commits the inputs and the updated state as public outputs. The
generator copies the exact 700 code bytes out of `weigh.elf` into a `.text.weigh`
section, so the routine ZisK proves is byte-identical to the one Lean proves.
The C wrapper needs a `clang` with the RISC-V target; assembly and linking use
the same GNU binutils as above.

```sh
.venv/bin/python scripts/zisk_guest.py
HWLOC_COMPONENTS=-gl .venv/bin/python scripts/benchmark_zisk.py --prove --gpu \
  --ziskemu <zisk>/bin/ziskemu --cargo-zisk <zisk>/bin/cargo-zisk-gpu \
  --proving-key <zisk>/provingKey
```

The compiler defaults to `clang`; set `CLANG` to another executable when the
one on `PATH` lacks the RISC-V target. The first command writes
`build/zisk/weigh-guest.elf` and, for each of the six benchmark scenarios in
`tests/weigh_cases.py`, `build/zisk/inputs/<scenario>.bin` (the guest input
record) and `build/zisk/inputs/<scenario>.public.bin` (the 64 public output
words the guest must commit, computed from the official reference).

The second command runs on a host with ZisK installed. `<zisk>` is the ZisK
installation directory (`~/.zisk` after `ziskup`); `--proving-key` names its
`provingKey` directory. Without `--prove` only `ziskemu` is needed and no GPU
is used. The script records symbol-level step counts from `ziskemu`, checks
the guest's public outputs against `<scenario>.public.bin`, and, with
`--prove`, times proof generation and verification. It writes
`build/zisk/results/report.json` and one log per tool invocation under
`build/zisk/results/logs`. `--scenarios` selects a subset by name; `--help`
lists the remaining options and defaults. `HWLOC_COMPONENTS=-gl` stops
hwloc's GL probe from waiting on an X11 socket.

The Lean proofs cover the modeled instruction sequence. ELF generation,
decoding, loading, execution-state conversion, and the ZisK wrapper are checked
by tests and are not formally proved. Benchmarks report RV64 instruction counts
separately from host interpreter time, and ZisK step counts separately from
GPU proving time; they do not measure native RV64 execution.
See [the recorded results and reproduction steps](docs/benchmarks.md).
