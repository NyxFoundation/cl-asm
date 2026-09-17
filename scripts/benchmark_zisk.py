"""Measure the ZisK guest: symbol-level steps, proof generation, and fixed overhead.

Runs on the proving host. Every tool invocation is logged to a file under the
output directory so no number in the report exists only on a terminal.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import struct
import subprocess
import sys
import time
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tests"))
from weigh_cases import benchmark_cases

PUBLIC_WORDS = 64


def logged(command: list, log: Path) -> tuple:
    """Run a command, save its output to a log, and return (wall seconds, output)."""
    start = time.monotonic()
    result = subprocess.run(command, capture_output=True, text=True, check=False)
    elapsed = time.monotonic() - start
    log.write_text(f"$ {' '.join(command)}\n--- stdout\n{result.stdout}\n--- stderr\n{result.stderr}\n"
                   f"--- exit {result.returncode} wall {elapsed:.3f}s\n")
    if result.returncode != 0:
        raise RuntimeError(f"{command[0]} failed; see {log}")
    return elapsed, result.stdout + result.stderr


def emulate(ziskemu: str, elf: Path, inputs: Path, log: Path) -> dict:
    """Symbol-level step counts and the ZisK cost model from the emulator's own report."""
    _, output = logged([ziskemu, "-e", str(elf), "-i", str(inputs), "-X", "-S"], log)
    steps = int(re.search(r"^STEPS\s+([\d,]+)", output, re.M).group(1).replace(",", ""))
    functions = function_table(output, "TOP STEP FUNCTIONS")
    costs = {name: int(value.replace(",", "")) for name, value in
             re.findall(r"^(MAIN|OPCODES|PRECOMPILES|MEMORY|VARIABLE|BASE|TOTAL)\s+([\d,]+)", output, re.M)}
    if "weigh" not in functions or "guest_main" not in functions:
        raise ValueError("emulator report lacks weigh or guest_main symbols")
    return {"steps": steps, "stepsByFunction": functions,
            "costByFunction": function_table(output, "TOP COST FUNCTIONS"), "cost": costs}


def function_table(output: str, heading: str) -> dict:
    """One per-symbol table from the ziskemu report: first column keyed by function name."""
    section = output.split(heading, 1)[1].split("\n\n", 1)[0]
    return {name: int(value.replace(",", "")) for value, name in
            re.findall(r"^\s+([\d,]+)\s+[\d.]+%\s+\d+\s+[\d,]+\s+(\w+)$", section, re.M)}


def public_outputs(ziskemu: str, elf: Path, inputs: Path, log: Path) -> list:
    _, output = logged([ziskemu, "-e", str(elf), "-i", str(inputs), "-c"], log)
    return [int(line, 16) for line in output.split() if re.fullmatch(r"[0-9a-f]{8}", line)]


def prove(cargo: str, elf: Path, inputs: Path, key: Path, proof: Path, gpu: bool, log: Path) -> dict:
    command = [cargo, "prove", "-e", str(elf), "-i", str(inputs), "-k", str(key),
               "-o", str(proof), "-vv"] + (["--gpu"] if gpu else [])
    wall, output = logged(command, log)
    stages = {name: int(ms) / 1000 for name, ms in re.findall(r"<<< ([A-Z_0-9]+) \((\d+)ms\)", output)}
    airs = {name: {"instances": int(count), "rowsLog2": int(log2)} for count, name, log2 in
            re.findall(r"(\d+) x Air \[(\w+)\] \(\d+ x 2\^(\d+)\)", output)}
    return {"wallSeconds": wall, "stageSeconds": stages, "airInstances": airs,
            "proofBytes": proof.stat().st_size,
            "proofSha256": hashlib.sha256(proof.read_bytes()).hexdigest()}


def verify(cargo: str, proof: Path, log: Path) -> dict:
    wall, _ = logged([cargo, "verify", "-p", str(proof)], log)
    return {"wallSeconds": wall}


def scenario(name: str, args, logs: Path) -> dict:
    inputs = args.guest / "inputs" / f"{name}.bin"
    expected = list(struct.unpack(f"<{PUBLIC_WORDS}I",
                                  (args.guest / "inputs" / f"{name}.public.bin").read_bytes()))
    elf = args.guest / "weigh-guest.elf"
    record = {"emulation": emulate(args.ziskemu, elf, inputs, logs / f"{name}.emulate.log")}
    publics = public_outputs(args.ziskemu, elf, inputs, logs / f"{name}.publics.log")
    if publics[:PUBLIC_WORDS] != expected:
        raise ValueError(f"{name}: guest public outputs differ from the official reference")
    record["publicOutputsMatchReference"] = True
    if args.prove:
        proof = args.output / f"{name}.proof"
        record["prove"] = prove(args.cargo_zisk, elf, inputs, args.proving_key, proof, args.gpu,
                                logs / f"{name}.prove.log")
        record["verify"] = verify(args.cargo_zisk, proof, logs / f"{name}.verify.log")
    return record


def environment(args) -> dict:
    cpu = next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                if line.startswith("model name")), platform.processor())
    gpu = subprocess.run(["nvidia-smi", "--query-gpu=name,driver_version,memory.total",
                          "--format=csv,noheader"], capture_output=True, text=True, check=False)
    version = subprocess.run([args.cargo_zisk, "--version"], capture_output=True, text=True, check=False)
    return {"hostname": platform.node(), "platform": platform.platform(), "cpu": cpu,
            "gpu": gpu.stdout.strip() if gpu.returncode == 0 else None,
            "zisk": version.stdout.strip() or version.stderr.strip(),
            "hwlocComponents": os.environ.get("HWLOC_COMPONENTS"),
            "guestElfSha256": hashlib.sha256((args.guest / "weigh-guest.elf").read_bytes()).hexdigest(),
            "embeddedWeighSha256": hashlib.sha256((args.guest / "embedded-weigh.bin").read_bytes()).hexdigest()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--guest", type=Path, default=ROOT / "build/zisk",
                        help="directory written by scripts/zisk_guest.py (weigh-guest.elf, inputs/)")
    parser.add_argument("--output", type=Path, default=ROOT / "build/zisk/results",
                        help="where report.json, proofs, and logs/ are written")
    parser.add_argument("--ziskemu", default=os.environ.get("ZISKEMU", "ziskemu"),
                        help="ziskemu executable, normally <zisk install>/bin/ziskemu (env ZISKEMU)")
    parser.add_argument("--cargo-zisk", default=os.environ.get("CARGO_ZISK", "cargo-zisk"),
                        help="cargo-zisk executable; use the -gpu build with --gpu (env CARGO_ZISK)")
    parser.add_argument("--proving-key", type=Path, default=Path.home() / ".zisk/provingKey",
                        help="ZisK proving-key directory from ziskup or cargo-zisk setup")
    parser.add_argument("--prove", action="store_true",
                        help="also run cargo-zisk prove and verify for each scenario")
    parser.add_argument("--gpu", action="store_true", help="pass --gpu to cargo-zisk prove")
    parser.add_argument("--scenarios", nargs="*", default=list(benchmark_cases()), metavar="NAME",
                        help="space-separated scenario names from tests/weigh_cases.py benchmark_cases()")
    args = parser.parse_args()
    logs = args.output / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    report = {"timestamp": datetime.now(timezone.utc).isoformat(), "environment": environment(args),
              "method": "ziskemu -X -S symbol steps and cost model; ziskemu -c public outputs "
                        "compared with the official reference; cargo-zisk prove wall time per "
                        "fresh process including proving-key loading; cargo-zisk verify wall time",
              "measurements": {}}
    for name in args.scenarios:
        report["measurements"][name] = scenario(name, args, logs)
        emulation = report["measurements"][name]["emulation"]
        line = f"{name}: weigh {emulation['stepsByFunction']['weigh']} steps of {emulation['steps']}"
        if args.prove:
            line += f"; prove {report['measurements'][name]['prove']['wallSeconds']:.2f}s wall"
        print(line)
        (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
