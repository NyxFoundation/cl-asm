"""The ZisK guest must wrap the checked weigh bytes and agree with the Lean decoder."""

import json
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest

from image_encoding import code_bytes
from official_oracle import evaluate
from weigh_cases import benchmark_cases, cases, make_case

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from zisk_guest import CFLAGS, build_guest, expected_publics, input_record, input_words, write_inputs

BUILD = ROOT / "build"
RUNNER = ROOT / ".lake/build/bin/cl-asm-weigh"
MAX_WORD = 2**64 - 1


def toolchain_available() -> bool:
    return all(shutil.which(tool) for tool in ["riscv64-unknown-elf-as", "riscv64-unknown-elf-ld", "clang"])


def elf_section(image: bytes, wanted: str) -> bytes:
    """Return one named section from a 64-bit little-endian ELF."""
    start = struct.unpack_from("<Q", image, 40)[0]
    size, count, names = struct.unpack_from("<HHH", image, 58)
    headers = [struct.unpack_from("<IIQQQQIIQQ", image, start + i * size) for i in range(count)]
    strings = headers[names]
    table = image[strings[4]:strings[4] + strings[5]]
    for header in headers:
        name = table[header[0]:table.index(b"\0", header[0])].decode()
        if name == wanted:
            return image[header[4]:header[4] + header[5]]
    raise KeyError(wanted)


def boundary_cases() -> list:
    """Admitted fixtures plus each precondition violated by exactly one."""
    limit = MAX_WORD // 3
    return cases()[:64] + [
        make_case(bits=16), make_case(previous_balance=limit + 1), make_case(current_balance=limit + 1),
        make_case(total=MAX_WORD // 2 + 1), make_case(previous_epoch=MAX_WORD - 2),
        make_case(current_epoch=MAX_WORD - 1), make_case(slot=0), make_case(slot=32),
        make_case(slot=33), make_case(slot=8192 + 1), make_case(slot=8192 + 32 + 1),
        make_case(slot=8192 + 32 + 2), make_case(slot=MAX_WORD, previous_balance=0, current_balance=0),
        make_case(slot=MAX_WORD - 8192 + 32, previous_balance=0),
    ]


@unittest.skipUnless(toolchain_available() and (BUILD / "weigh.elf").exists(),
                     "requires clang, GNU RISC-V binutils, and a generated weigh.elf")
class ZiskGuestImageTests(unittest.TestCase):
    def test_should_embed_exactly_the_checked_weigh_code_bytes(self):
        with tempfile.TemporaryDirectory(prefix="cl-asm-zisk-") as directory:
            elf = build_guest(BUILD, Path(directory)).read_bytes()
        self.assertEqual(elf_section(elf, ".text.weigh"), code_bytes((BUILD / "weigh.elf").read_bytes()))
        self.assertEqual(struct.unpack_from("<Q", elf, 24)[0], 0x80000000)

    def test_should_place_the_routine_at_a_fixed_address_after_start(self):
        with tempfile.TemporaryDirectory(prefix="cl-asm-zisk-") as directory:
            elf = build_guest(BUILD, Path(directory)).read_bytes()
        start = elf_section(elf, ".text.start")
        self.assertEqual(len(start) % 4, 0)
        self.assertLess(len(start), 64)


class ZiskGuestInputTests(unittest.TestCase):
    def test_should_encode_fixture_words_in_abi_order(self):
        data = make_case(slot=1000, bits=5, previous_balance=7, current_balance=9)
        record = input_record(data)
        self.assertEqual(struct.unpack_from("<Q", record)[0], 21 * 8)
        words = list(struct.unpack_from("<21Q", record, 8))
        self.assertEqual(words[0], 1000)
        self.assertEqual(words[1], 5)
        self.assertEqual(words[2:7], [5, 11, 22, 33, 44])
        self.assertEqual(words[7:12], [7, 55, 66, 77, 88])
        self.assertEqual(words[12:17], [0, 99, 111, 222, 333])
        self.assertEqual(words[17:21], [96, 7, 9, 0x1122334455667788])

    def test_should_derive_public_outputs_from_the_official_reference(self):
        for name, data in benchmark_cases().items():
            with self.subTest(scenario=name):
                publics = expected_publics(data)
                result = evaluate(data)
                self.assertEqual(publics[0], 1)
                self.assertEqual(publics[43], result["bits"])
                current = publics[44] | publics[45] << 32
                finalized = publics[54] | publics[55] << 32
                self.assertEqual(current, result["current"]["epoch"])
                self.assertEqual(finalized, result["finalized"]["epoch"])
                for i, value in enumerate(input_words(data)):
                    self.assertEqual(publics[1 + 2 * i] | publics[2 + 2 * i] << 32, value)

    def test_should_write_one_input_and_expected_public_file_per_scenario(self):
        with tempfile.TemporaryDirectory(prefix="cl-asm-zisk-") as directory:
            paths = write_inputs(Path(directory))
            self.assertEqual(set(paths), set(benchmark_cases()))
            for name, path in paths.items():
                self.assertEqual(path.stat().st_size, 8 + 21 * 8)
                self.assertEqual((path.parent / f"{name}.public.bin").stat().st_size, 256)


@unittest.skipUnless(shutil.which("clang") and RUNNER.exists() and (BUILD / "weigh.elf").exists(),
                     "requires clang and the built Lean runner")
class ZiskGuestValidityTests(unittest.TestCase):
    HARNESS = ("#include <stdio.h>\n#include \"input.h\"\nint main(void){uint64_t w[INPUT_WORDS];"
               "for(unsigned i=0;i<INPUT_WORDS;++i){if(scanf(\"%llu\",(unsigned long long*)&w[i])!=1)"
               "return 2;}return input_valid(w)?0:1;}\n")

    def lean_accepts(self, data: dict) -> bool:
        result = subprocess.run([str(RUNNER), str(BUILD / "weigh.elf")], input=json.dumps(data) + "\n",
                                text=True, capture_output=True, check=False)
        return result.returncode == 0

    def test_should_reject_exactly_the_inputs_the_lean_decoder_rejects(self):
        with tempfile.TemporaryDirectory(prefix="cl-asm-zisk-") as directory:
            source = Path(directory) / "check.c"
            source.write_text(self.HARNESS)
            binary = Path(directory) / "check"
            flags = [flag for flag in CFLAGS if not flag.startswith(("--target", "-march", "-mabi", "-mno-relax", "-mcmodel",
                                                                      "-ffreestanding", "-nostdlib", "-fno-builtin"))]
            subprocess.run(["clang", *flags, "-I", str(ROOT / "guest/zisk"), str(source), "-o", str(binary)],
                           check=True, capture_output=True)
            verdicts = []
            for data in boundary_cases():
                words = " ".join(str(word) for word in input_words(data))
                guest = subprocess.run([str(binary)], input=words, text=True, check=False).returncode == 0
                verdicts.append((guest, self.lean_accepts(data)))
        self.assertTrue(any(accepted for accepted, _ in verdicts) and not all(accepted for accepted, _ in verdicts))
        for index, (guest, lean) in enumerate(verdicts):
            self.assertEqual(guest, lean, f"case {index} verdict differs")
