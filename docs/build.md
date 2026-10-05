---
title: Build, Validate, and Run the ZisK Guest
last_updated: 2026-10-05
tags:
  - build
  - testing
  - zisk
---

# Build, Validate, and Run the ZisK Guest

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

Helper cases are in [the helper contracts](helpers.md). Full-routine cases are in
[the whole-routine contract](weigh.md).

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

Trust boundaries are in
[the bootstrap contract](bootstrap.md#validation-and-trust-boundaries). Scope is in
[the completion plan](implementation-plan.md).
See [the recorded results](benchmarks.md).
