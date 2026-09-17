"""Build the ZisK guest around the checked weigh ELF and write scenario inputs."""

import argparse
import os
from pathlib import Path
import struct
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tests"))
from image_encoding import code_bytes, validate
from official_oracle import evaluate
from weigh_cases import benchmark_cases

GUEST = ROOT / "guest/zisk"
INPUT_WORDS = 21
PUBLIC_WORDS = 64
CFLAGS = ["--target=riscv64-unknown-elf", "-march=rv64im", "-mabi=lp64", "-mno-relax", "-mcmodel=medany",
          "-ffreestanding", "-nostdlib", "-fno-builtin", "-fno-stack-protector", "-O2",
          "-Wall", "-Wextra", "-Werror"]


def tool(name: str, default: str) -> str:
    return os.environ.get(name, default)


def run(*args: str) -> None:
    subprocess.run(list(args), check=True, capture_output=True)


def embed_source(binary: Path) -> str:
    return (".option norvc\n.option norelax\n"
            ".section .text.weigh,\"ax\",@progbits\n.balign 4\n"
            ".globl weigh\n.type weigh, @function\nweigh:\n"
            f".incbin \"{binary}\"\n.size weigh, . - weigh\n")


def build_guest(build: Path, output: Path) -> Path:
    """Link the proved routine's exact code bytes with the C wrapper."""
    validate(build)
    output.mkdir(parents=True, exist_ok=True)
    code = code_bytes((build / "weigh.elf").read_bytes())
    embedded = output / "embedded-weigh.bin"
    embedded.write_bytes(code)
    (output / "weigh-embed.s").write_text(embed_source(embedded.resolve()))
    assembler = tool("RISCV_AS", "riscv64-unknown-elf-as")
    linker = tool("RISCV_LD", "riscv64-unknown-elf-ld")
    clang = tool("CLANG", "clang")
    run(clang, *CFLAGS, "-c", str(GUEST / "main.c"), "-o", str(output / "main.o"))
    for name in ["start", "weigh-embed"]:
        source = GUEST / f"{name}.s" if name == "start" else output / f"{name}.s"
        run(assembler, "-march=rv64im", "-mabi=lp64", "-mno-relax", "--fatal-warnings",
            "-o", str(output / f"{name}.o"), str(source))
    elf = output / "weigh-guest.elf"
    run(linker, "-m", "elf64lriscv", "--no-relax", "--fatal-warnings", "-T", str(GUEST / "link.ld"),
        "-o", str(elf), str(output / "start.o"), str(output / "weigh-embed.o"), str(output / "main.o"))
    return elf


def checkpoint_words(data: dict) -> list:
    return [data["epoch"], *data["root"]]


def input_words(data: dict) -> list:
    """The guest input record: 17 state words, three balances, and the root seed."""
    words = [data["slot"], data["bits"], *checkpoint_words(data["previous"]),
             *checkpoint_words(data["current"]), *checkpoint_words(data["finalized"]),
             data["total"], data["previousBalance"], data["currentBalance"], data["rootSeed"]]
    if len(words) != INPUT_WORDS:
        raise ValueError("unexpected input word count")
    return words


def expected_publics(data: dict) -> list:
    """Mirror the guest's commit(): success flag, all inputs, then the updated bits,
    current checkpoint, and finalized checkpoint as 32-bit words."""
    result = evaluate(data)
    words = [1]
    for value in input_words(data):
        words += [value & 0xFFFFFFFF, value >> 32]
    words.append(result["bits"])
    for value in checkpoint_words(result["current"]) + checkpoint_words(result["finalized"]):
        words += [value & 0xFFFFFFFF, value >> 32]
    if len(words) != PUBLIC_WORDS:
        raise ValueError("unexpected public output word count")
    return words


def input_record(data: dict) -> bytes:
    words = input_words(data)
    return struct.pack("<Q", 8 * len(words)) + struct.pack(f"<{len(words)}Q", *words)


def write_inputs(output: Path) -> dict:
    directory = output / "inputs"
    directory.mkdir(parents=True, exist_ok=True)
    paths = {}
    for name, data in benchmark_cases().items():
        (directory / f"{name}.bin").write_bytes(input_record(data))
        (directory / f"{name}.public.bin").write_bytes(
            struct.pack(f"<{PUBLIC_WORDS}I", *expected_publics(data)))
        paths[name] = directory / f"{name}.bin"
    return paths


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, default=ROOT / "build")
    parser.add_argument("--output", type=Path, default=ROOT / "build/zisk")
    args = parser.parse_args()
    elf = build_guest(args.build, args.output)
    inputs = write_inputs(args.output)
    print(f"Generated {elf}")
    for path in inputs.values():
        print(f"Generated {path}")


if __name__ == "__main__":
    main()
