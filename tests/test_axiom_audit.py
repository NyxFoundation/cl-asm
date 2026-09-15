"""The audit must reject unused forbidden axioms, including private declarations."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class AxiomAuditTests(unittest.TestCase):
    def assert_forbidden_axiom_rejected(self, visibility: str) -> None:
        source = (ROOT / "scripts/CheckAxioms.lean").read_text()
        injection = f"namespace ClAsm\n{visibility}axiom forbiddenAuditFixture : False\nend ClAsm\n"
        source = source.replace("open Lean in", injection + "\nopen Lean in", 1)
        with tempfile.TemporaryDirectory(prefix="cl-asm-axioms-") as directory:
            path = Path(directory) / "Check.lean"
            path.write_text(source)
            result = subprocess.run(
                [os.environ.get("LAKE", "lake"), "env", "lean", str(path)],
                cwd=ROOT, capture_output=True, text=True, check=False,
            )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("depends on unapproved axiom", result.stdout)
        self.assertIn("forbiddenAuditFixture", result.stdout)
        self.assertNotIn("Axiom audit passed", result.stdout)

    def test_should_reject_unused_public_axiom(self) -> None:
        self.assert_forbidden_axiom_rejected("")

    def test_should_reject_unused_private_axiom(self) -> None:
        self.assert_forbidden_axiom_rejected("private ")


if __name__ == "__main__":
    unittest.main()
