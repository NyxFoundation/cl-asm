"""Independent RV64 encoding and GNU .word assembly for modeled Programs."""

import json
import os
from pathlib import Path
import struct
import subprocess
import tempfile


def encode_instruction(instruction):
    operation, operands = instruction
    a, b = operands[:2]
    c = operands[2] if len(operands) == 3 else 0
    r_forms = {"ADD": 0, "SLTU": 3, "XOR": 4, "AND": 7}
    i_forms = {"ADDI": (0x13, 0), "SLTIU": (0x13, 3), "XORI": (0x13, 4),
               "ORI": (0x13, 6), "ANDI": (0x13, 7), "SLLI": (0x13, 1),
               "SRLI": (0x13, 5), "LD": (0x03, 3), "JALR": (0x67, 0)}
    if operation in r_forms:
        return 0x33 | a << 7 | r_forms[operation] << 12 | b << 15 | c << 20
    if operation in i_forms:
        opcode, funct3 = i_forms[operation]
        return opcode | a << 7 | funct3 << 12 | b << 15 | (c & 0xFFF) << 20
    if operation == "SD":
        return 0x23 | (c & 31) << 7 | 3 << 12 | a << 15 | b << 20 | ((c >> 5) & 127) << 25
    if operation == "BNE":
        return (0x63 | ((c >> 11) & 1) << 7 | ((c >> 1) & 15) << 8 | 1 << 12 |
                a << 15 | b << 20 | ((c >> 5) & 63) << 25 | ((c >> 12) & 1) << 31)
    if operation == "JAL":
        return (0x6F | a << 7 | ((b >> 12) & 255) << 12 | ((b >> 11) & 1) << 20 |
                ((b >> 1) & 1023) << 21 | ((b >> 20) & 1) << 31)
    raise ValueError(f"unsupported independent encoding: {operation}")


def code_bytes(image: bytes) -> bytes:
    if image[:7] != b"\x7fELF\x02\x01\x01" or struct.unpack_from("<H", image, 18)[0] != 243:
        raise ValueError("unexpected ELF format")
    if struct.unpack_from("<Q", image, 24)[0] != 0x80000000:
        raise ValueError("unexpected entry address")
    start = struct.unpack_from("<Q", image, 32)[0]
    size, count = struct.unpack_from("<HH", image, 54)
    loads = [start + i * size for i in range(count)
             if struct.unpack_from("<I", image, start + i * size)[0] == 1]
    if len(loads) != 1:
        raise ValueError("expected one loadable segment")
    kind, flags, offset, address, _, filesz, memsz, _ = struct.unpack_from("<IIQQQQQQ", image, loads[0])
    if flags != 5 or address != 0x80000000 or filesz != memsz or offset + filesz > len(image):
        raise ValueError("unexpected code placement, permissions, or extent")
    return image[offset:offset + filesz]


def reference_bytes(program, linker_script: Path) -> bytes:
    words = [encode_instruction(instruction) for instruction in program]
    with tempfile.TemporaryDirectory(prefix="cl-asm-encoding-") as directory:
        source, obj, elf = [Path(directory) / f"reference.{suffix}" for suffix in ["s", "o", "elf"]]
        source.write_text(".section .text\n.globl weigh\nweigh:\n" +
                          "".join(f".word 0x{word:08x}\n" for word in words))
        subprocess.run([os.environ.get("RISCV_AS", "riscv64-unknown-elf-as"),
                        "-march=rv64im", "-mabi=lp64", "-mno-relax", "--fatal-warnings",
                        "-o", str(obj), str(source)], check=True, capture_output=True)
        subprocess.run([os.environ.get("RISCV_LD", "riscv64-unknown-elf-ld"),
                        "--no-relax", "--fatal-warnings", "-T", str(linker_script),
                        "-o", str(elf), str(obj)], check=True, capture_output=True)
        assembled = code_bytes(elf.read_bytes())
    if assembled != b"".join(struct.pack("<I", word) for word in words):
        raise ValueError("reference assembly changed instruction words")
    return assembled


def validate(directory: Path) -> None:
    program = json.loads((directory / "weigh.program.json").read_text())
    for index, (operation, operands) in enumerate(program):
        if operation in {"BNE", "JAL"}:
            offset = operands[-1]
            if offset <= 0 or offset % 4 or index + offset // 4 >= len(program):
                raise ValueError("invalid branch target")
    actual = code_bytes((directory / "weigh.elf").read_bytes())
    expected = reference_bytes(program, directory / "weigh.ld")
    if actual != expected:
        raise ValueError("independently assembled Program differs from weigh ELF")
