"""Measure checked ELF scenarios, keeping RV64 counts and host timing separate."""

import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path
import platform
import statistics
import subprocess
import sys
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tests"))
from official_oracle import evaluate
from weigh_cases import benchmark_cases
from image_encoding import code_bytes, validate


def command(*args):
    return subprocess.check_output(args, text=True, cwd=ROOT).strip()


def measure(iterations, batches):
    scenarios = benchmark_cases()
    elf = ROOT / "build/weigh.elf"
    result = subprocess.run([str(ROOT / ".lake/build/bin/cl-asm-weigh"), str(elf),
        "--benchmark", str(iterations), str(batches)],
        input="".join(json.dumps(data) + "\n" for data in scenarios.values()),
        text=True, capture_output=True, check=True)
    measurements = {}
    outputs = result.stdout.splitlines()
    if len(outputs) != len(scenarios):
        raise ValueError("benchmark output count mismatch")
    for (name, data), line in zip(scenarios.items(), outputs, strict=True):
        record = json.loads(line)
        observed = dict(record["result"])
        observed.pop("steps")
        if observed != evaluate(data):
            raise ValueError(f"official reference mismatch in {name}")
        per_call = [duration / iterations for duration in record["batchNanoseconds"]]
        measurements[name] = {**record, "medianNanosecondsPerCall": statistics.median(per_call),
                              "minNanosecondsPerCall": min(per_call),
                              "maxNanosecondsPerCall": max(per_call)}
    return measurements


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--iterations", type=int, default=200)
    parser.add_argument("--batches", type=int, default=21)
    parser.add_argument("--output", type=Path, default=ROOT / "build/benchmark.json")
    args = parser.parse_args()
    validate(ROOT / "build")
    cpu = next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                if line.startswith("model name")), platform.processor())
    report = {"timestamp": datetime.now(timezone.utc).isoformat(),
        "revision": command("git", "rev-parse", "HEAD"),
        "workingTreeDirty": bool(command("git", "status", "--porcelain")),
        "elfSha256": hashlib.sha256((ROOT / "build/weigh.elf").read_bytes()).hexdigest(),
        "instructionBytes": len(code_bytes((ROOT / "build/weigh.elf").read_bytes())),
        "platform": platform.platform(), "cpu": cpu,
        "python": platform.python_version(), "lean": (ROOT / "lean-toolchain").read_text().strip(),
        "ssz": importlib.metadata.version("eth-ssz-specs"),
        "method": "100 warmup calls; batches exclude loading, input preparation, JSON, and full preservation checks; include interpreter, temporary-register reset, checksum; no zkVM proving or native RV64 timing",
        "measurements": measure(args.iterations, args.batches)}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for name, record in report["measurements"].items():
        print(f"{name}: {record['result']['steps']} RV64 steps; "
              f"{record['medianNanosecondsPerCall'] / 1000:.2f} us median host interpreter time")


if __name__ == "__main__":
    main()
