"""Differential tests against the pinned official function, including failure boundaries."""

import json
from pathlib import Path
import subprocess
import unittest

from official_oracle import evaluate
from weigh_cases import MAX_WORD, cases, make_case


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / ".lake/build/bin/cl-asm-weigh"
ELF = ROOT / "build/weigh.elf"


def run_inputs(inputs):
    return subprocess.run([str(RUNNER), str(ELF)],
        input="".join(json.dumps(value) + "\n" for value in inputs),
        text=True, capture_output=True, check=False)


class WeighTests(unittest.TestCase):
    def test_should_match_official_function_for_all_admitted_cases(self):
        inputs = cases()
        result = run_inputs(inputs)
        self.assertEqual(result.returncode, 0, result.stderr)
        outputs = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(outputs), len(inputs))
        steps = set()
        for index, (data, actual) in enumerate(zip(inputs, outputs, strict=True)):
            with self.subTest(index=index):
                steps.add(actual.pop("steps"))
                self.assertEqual(actual, evaluate(data))
        self.assertEqual(min(steps), 99)
        self.assertEqual(max(steps), 147)
        print(f"weigh: {len(inputs)} official differential cases; {min(steps)}..{max(steps)} steps")

    def test_should_reject_overflow_and_temporal_inputs_outside_contract(self):
        inputs = [make_case(total=MAX_WORD), make_case(previous_balance=MAX_WORD // 3 + 1),
                  make_case(current_balance=MAX_WORD // 3 + 1),
                  make_case(previous_epoch=MAX_WORD - 2), make_case(current_epoch=MAX_WORD - 1),
                  make_case(slot=0), make_case(slot=32), make_case(slot=MAX_WORD)]
        for data in inputs:
            with self.subTest(data=data):
                self.assertNotEqual(run_inputs([data]).returncode, 0)
                with self.assertRaises((ValueError, AssertionError)):
                    evaluate(data)

    def test_should_reject_noncanonical_or_malformed_input(self):
        malformed = make_case()
        malformed["current"]["root"] = [1, 2, 3]
        for data in [make_case(bits=16), make_case(slot=2**64), malformed]:
            with self.subTest(data=data):
                self.assertNotEqual(run_inputs([data]).returncode, 0)


if __name__ == "__main__":
    unittest.main()
