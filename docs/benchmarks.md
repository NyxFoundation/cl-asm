---
title: Weigh Benchmark Results
last_updated: 2026-09-13
tags:
  - benchmark
  - consensus
  - riscv
---

# Weigh Benchmark Results

The complete checked `weigh.elf` uses 99–147 modeled RV64 instructions across
these scenarios. On the host below, the median batch-average interpreter time
was 2.212–4.999 ms per call. The proved static bound is 175 instructions and the
executable code is 700 bytes.

| Scenario | RV64 steps | Median ms/call | Min–max batch average ms/call |
|---|---:|---:|---:|
| No updates | 99 | 2.212 | 2.072–2.452 |
| Previous justified | 112 | 2.987 | 2.823–3.351 |
| Current justified | 112 | 3.019 | 2.860–3.331 |
| Both justified | 125 | 3.683 | 3.504–4.035 |
| Two finalization overwrites | 147 | 4.999 | 4.853–5.624 |
| Genesis, shared previous/current root | 125 | 3.609 | 3.511–4.091 |

## Artifact and environment

- Source: `8bd979798a735ac094cd45bf55cffe4b1a676935`, clean working tree.
- ELF SHA-256: `5ed4f9c4c39b56d8149ee744bc39ab62fe84a172e39311ea11480c2cafe961af`.
- Host: AMD Ryzen 9 PRO 8945HS; Linux 7.0.12, x86-64, glibc 2.42.
- Lean 4.33.0; its bundled Clang 22.1.4; GNU RISC-V assembler/linker 2.46.
- Python 3.12.13; `eth-ssz-specs` 0.1.0 and the pinned test requirements.
- Measurement began at 2026-09-13 10:19:32 UTC.

[Raw results](benchmarks/2026-09-13.json) retain all 21 batch durations per
scenario, checksums, resulting states, instruction counts, and metadata.
Fixtures are `benchmark_cases()` in `tests/weigh_cases.py` at the recorded revision.

## Method and reproduction

Build the measured revision using the [README instructions](../README.md),
including the pinned Python environment and RISC-V binutils. Then run:

```sh
.venv/bin/python scripts/benchmark.py --iterations 200 --batches 21
```

`RISCV_AS` and `RISCV_LD` can select explicit binutils paths. The script validates
the independently assembled ELF bytes and compares scenario results with the
official function. Each scenario runs 100 warmup calls and 21 batches of 200
calls. Timings use `IO.monoNanosNow`; the table reports the median and range of
the 21 batch averages, rather than individual-call latency percentiles.

The timed section includes interpreter execution, resetting one overwritten
temporary register, and an observable result checksum. ELF loading, preparing
the state/root array, JSON handling, and full preservation checks occur outside
that section. Full state, scratch, frame, and fuel validation runs before timing.
No local build or test suite ran during this measurement. Host scheduling and
CPU frequency were not controlled.

These are host interpreter measurements. Native RV64 performance, zkVM proving
cost, and formal ELF correspondence are outside this measurement's scope.
