"""Ensure image and process failures cannot be reported as successful validation."""

import os
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / ".lake/build/bin/cl-asm-test"
GENERATOR = ROOT / ".lake/build/bin/cl-asm"
ELF = ROOT / "build/epoch-at-slot.elf"


class ElfRejectionTests(unittest.TestCase):
    def assert_rejected(
        self, image: bytes, reason: str, probe: str = "epoch-at-slot"
    ) -> None:
        with tempfile.TemporaryDirectory(prefix="cl-asm-test-") as directory:
            path = Path(directory) / "mutated.elf"
            path.write_bytes(image)
            result = subprocess.run(
                [str(RUNNER), probe, str(path)],
                capture_output=True, text=True, check=False
            )
        self.assertEqual(result.returncode, 1)
        self.assertIn(reason, result.stderr)
        self.assertNotIn("PASS:", result.stdout)

    def mutate(self, offset: int, value: int, width: str = "Q") -> bytes:
        image = bytearray(ELF.read_bytes())
        struct.pack_into("<" + width, image, offset, value)
        return bytes(image)

    def program_header(self) -> int:
        image = ELF.read_bytes()
        base = struct.unpack_from("<Q", image, 0x20)[0]
        size, count = struct.unpack_from("<HH", image, 0x36)
        loads = [base + i * size for i in range(count)
                 if struct.unpack_from("<I", image, base + i * size)[0] == 1]
        self.assertEqual(len(loads), 1)
        return loads[0]

    def test_should_reject_truncated_elf_when_header_is_incomplete(self) -> None:
        self.assert_rejected(ELF.read_bytes()[:20], "too small")

    def test_should_reject_image_when_magic_is_wrong(self) -> None:
        self.assert_rejected(self.mutate(0, 0, "I"), "bad magic")

    def test_should_reject_image_when_architecture_is_wrong(self) -> None:
        self.assert_rejected(self.mutate(0x12, 62, "H"), "e_machine")

    def test_should_reject_image_when_entry_is_shifted(self) -> None:
        self.assert_rejected(self.mutate(0x18, 0x80000004), "ELF entry mismatch")

    def test_should_reject_image_when_segment_address_is_shifted(self) -> None:
        self.assert_rejected(
            self.mutate(self.program_header() + 0x10, 0x80000004), "ELF code address mismatch"
        )

    def test_should_reject_image_when_code_is_writable(self) -> None:
        self.assert_rejected(
            self.mutate(self.program_header() + 4, 7, "I"), "ELF code permissions mismatch"
        )

    def test_should_reject_image_when_segment_extent_grows(self) -> None:
        self.assert_rejected(
            self.mutate(self.program_header() + 0x28, 16), "ELF code extent mismatch"
        )

    def test_should_reject_image_when_instruction_operand_changes(self) -> None:
        offset = struct.unpack_from("<Q", ELF.read_bytes(), self.program_header() + 8)[0]
        self.assert_rejected(self.mutate(offset + 4, 0x0062D293, "I"), "instruction bytes mismatch")

    def test_should_reject_every_probe_when_return_instruction_changes(self) -> None:
        probes = ["epoch-at-slot", "previous-epoch", "shift-justification-bits",
                  "has-supermajority", "block-root-address", "copy-checkpoint", "copy-root"]
        for probe in probes:
            with self.subTest(probe=probe):
                image = bytearray((ROOT / "build" / f"{probe}.elf").read_bytes())
                base = struct.unpack_from("<Q", image, 0x20)[0]
                size, count = struct.unpack_from("<HH", image, 0x36)
                header = next(base + i * size for i in range(count)
                              if struct.unpack_from("<I", image, base + i * size)[0] == 1)
                offset = struct.unpack_from("<Q", image, header + 8)[0]
                length = struct.unpack_from("<Q", image, header + 0x20)[0]
                struct.pack_into("<I", image, offset + length - 4, 0x0000006F)
                self.assert_rejected(bytes(image), "instruction bytes mismatch", probe)

    def test_should_fail_generation_when_assembler_fails(self) -> None:
        with tempfile.TemporaryDirectory(prefix="cl-asm-test-") as directory:
            result = subprocess.run(
                [str(GENERATOR), directory],
                env={**os.environ, "RISCV_AS": "/bin/false"},
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(result.returncode, 1)
            self.assertFalse((Path(directory) / "epoch-at-slot.elf").exists())
            self.assertIn("ELF generation failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
