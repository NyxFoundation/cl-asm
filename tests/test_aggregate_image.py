"""Independent bytes, branch destinations, and fail-closed ELF admission."""

import json
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest

from image_encoding import code_bytes, encode_instruction, reference_bytes
from test_aggregate import ELF, ROOT, RUNNER

BUILD = ROOT / "build"


class AggregateImageTests(unittest.TestCase):
    def test_should_match_independent_encoding_when_program_is_assembled(self):
        program = json.loads((BUILD / "aggregate.program.json").read_text())
        self.assertEqual(len(program), 78)
        expected = reference_bytes(program, BUILD / "aggregate.ld", "aggregate")
        self.assertEqual(len(expected), 312)
        self.assertEqual(code_bytes(ELF.read_bytes()), expected)
        for index, (operation, operands) in enumerate(program):
            if operation in {"BNE", "JAL"}:
                offset = operands[-1]
                self.assertEqual(offset % 4, 0)
                self.assertTrue(0 <= index + offset // 4 < len(program))
        self.assertEqual(program[9], ["BNE", [13, 0, 8]])
        self.assertEqual(program[10], ["JAL", [0, 208]])
        self.assertEqual(program[61], ["JAL", [0, -208]])
        self.assertEqual(encode_instruction(["LUI", [28, 0x3B9AD]]), 0x3B9ADE37)
        self.assertEqual(encode_instruction(["SUB", [7, 0, 5]]), 0x405003B3)

    def test_should_reject_images_when_code_or_layout_is_mutated(self):
        image = ELF.read_bytes()
        header_base = struct.unpack_from("<Q", image, 32)[0]
        header_size, count = struct.unpack_from("<HH", image, 54)
        header = next(header_base + i * header_size for i in range(count)
                      if struct.unpack_from("<I", image, header_base + i * header_size)[0] == 1)
        code_offset = struct.unpack_from("<Q", image, header + 8)[0]
        mutations = [(24, "Q", 0x80000004), (header + 16, "Q", 0x80000004),
                     (header + 4, "I", 7), (header + 40, "Q", 316),
                     (header + 32, "Q", 308), (code_offset + 61 * 4, "I", 0x0000006F),
                     (code_offset + 77 * 4, "I", 0x0000006F),
                     (code_offset + 7 * 4, "I", 0x00000E37)]
        altered = [image[:20], (BUILD / "weigh.elf").read_bytes()]
        for offset, fmt, value in mutations:
            data = bytearray(image)
            struct.pack_into("<" + fmt, data, offset, value)
            altered.append(bytes(data))
        with tempfile.TemporaryDirectory(prefix="cl-asm-aggregate-") as directory:
            path = Path(directory) / "mutated.elf"
            for index, data in enumerate(altered):
                with self.subTest(index=index):
                    path.write_bytes(data)
                    result = subprocess.run([str(RUNNER), str(path)], input="",
                                            text=True, capture_output=True, check=False)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
