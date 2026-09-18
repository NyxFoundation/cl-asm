# CL ASM

Lean proofs and RISC-V code for Ethereum consensus-layer operations. The v0
target is `weigh_justification_and_finalization`: a 175-instruction RV64
routine (700 bytes) whose Lean contract proves the specified state transition,
resource preservation, and return within 175 steps. The same bytes run as a
ZisK zkVM guest.

- [DESIGN.md](DESIGN.md): scope, ABI, memory layout, trust boundaries.
- [Roadmap](docs/roadmap.md): why the consensus layer is being proved, zkVM
  findings, PoC decisions, and remaining work.
- [Whole-routine contract](docs/weigh.md): preconditions, calling witness,
  official-reference tests.
- [Build and validate](docs/build.md): toolchain, commands, test coverage, and
  the ZisK guest.
- [Benchmarks](docs/benchmarks.md): host interpreter timing and ZisK results.

```sh
lake --no-cache --wfail build
python3 -m venv .venv && .venv/bin/python -m pip install -r tests/requirements.txt
.lake/build/bin/cl-asm build && .lake/build/bin/cl-asm-test build
.venv/bin/python -m unittest discover -s tests -v
```

Requires elan (Lean 4.33.0 is pinned), Python 3.12+, GNU RISC-V binutils, and
a `clang` with the RISC-V target for the ZisK guest.

The Lean proofs cover the modeled instruction sequence. ELF generation, loading,
the interpreter conversion, and the ZisK wrapper are checked by tests, not
proved.
