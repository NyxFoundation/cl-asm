import json
from pathlib import Path
import struct
import unittest

from image_encoding import code_bytes, encode_instruction, validate


BUILD = Path(__file__).resolve().parents[1] / "build"


class WeighImageTests(unittest.TestCase):
    def test_should_match_independently_assembled_program_and_branch_targets(self):
        validate(BUILD)

    def test_should_detect_changed_branch_operand(self):
        program = json.loads((BUILD / "weigh.program.json").read_text())
        branch = next(index for index, (operation, _) in enumerate(program) if operation == "BNE")
        program[branch][1][-1] += 4
        altered = b"".join(struct.pack("<I", encode_instruction(instruction)) for instruction in program)
        self.assertNotEqual(altered, code_bytes((BUILD / "weigh.elf").read_bytes()))
