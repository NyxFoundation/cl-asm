"""Differential and admission checks through the generated ELF runner."""

import json
from pathlib import Path
import subprocess
import unittest

from aggregate_cases import INCREMENT, MAX_WORD, cases, make_case, validator
from official_oracle import evaluate_aggregate

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / ".lake/build/bin/cl-asm-aggregate"
ELF = ROOT / "build/aggregate.elf"


def run_inputs(inputs, *args):
    return subprocess.run([str(RUNNER), str(ELF), *args],
                          input="".join(json.dumps(value) + "\n" for value in inputs),
                          text=True, capture_output=True, check=False, timeout=120)


class AggregateTests(unittest.TestCase):
    def test_should_show_usage_when_arguments_are_missing_or_invalid(self):
        for args in [[], [str(ELF), "--unknown"],
                     [str(ELF), "--benchmark", "invalid", "1"]]:
            with self.subTest(args=args):
                result = subprocess.run([str(RUNNER), *args], input="", text=True,
                                        capture_output=True, check=False, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn("usage: cl-asm-aggregate <aggregate.elf>", result.stderr)

    def test_should_match_official_reference_and_exact_steps_when_inputs_are_admitted(self):
        inputs = cases()
        result = run_inputs(inputs)
        self.assertEqual(result.returncode, 0, result.stderr)
        outputs = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(outputs), len(inputs))
        for data, actual in zip(inputs, outputs, strict=True):
            with self.subTest(slot=data["slot"], count=len(data["validators"])):
                expected = evaluate_aggregate(data)
                steps = actual.pop("steps")
                self.assertEqual(actual, expected)
                raw = raw_sums(data)
                self.assertEqual(steps, 21 + 52 * len(data["validators"]) +
                                 sum(value >= INCREMENT for value in raw.values()))

    def test_should_reject_malformed_and_overflowing_inputs(self):
        invalid = [make_case(slot=2**64), make_case(slot=-1),
                   make_case(previous=[]), make_case(current=[2, 2]),
                   make_case(previous=[256]), make_case(current=[-1]),
                   make_case([validator(slashed=2)]),
                   make_case([validator(balance=2**64)]),
                   make_case([validator(activation=2**64)]),
                   make_case([validator(exit_epoch=2**64)]),
                   make_case([validator(MAX_WORD), validator(1)]),
                   make_case([validator(MAX_WORD, exit_epoch=3),
                              validator(1, exit_epoch=3)], slot=96),
                   make_case([validator()] * 32769)]
        malformed = make_case()
        del malformed["validators"][0]["exitEpoch"]
        invalid.extend([malformed, {}, None])
        for data in invalid:
            with self.subTest(data=str(data)[:160]):
                result = run_inputs([data])
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

    def test_should_accept_capacity_boundary_without_stack_overflow(self):
        data = make_case([validator(0)] * 32768)
        result = run_inputs([data])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout),
                         {"total": INCREMENT, "previous": INCREMENT, "current": INCREMENT,
                          "steps": 21 + 52 * 32768})

    def test_should_measure_repeated_execution_with_checked_checksum(self):
        data = make_case()
        result = run_inputs([data], "--benchmark", "2", "3")
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report["iterationsPerBatch"], 2)
        self.assertEqual(len(report["batchNanoseconds"]), 3)
        self.assertTrue(all(t > 0 for t in report["batchNanoseconds"]))
        self.assertEqual(report["result"]["total"], 32 * INCREMENT)
        self.assertEqual(report["checksum"], 6 * (report["result"]["steps"] + 32 * INCREMENT))
        for args in [("0", "1"), ("1", "0"), ("100001", "1"), ("1", "1001")]:
            self.assertNotEqual(run_inputs([data], "--benchmark", *args).returncode, 0)


def raw_sums(data):
    epoch = data["slot"] // 32

    def active(v, at):
        return v["activationEpoch"] <= at < v["exitEpoch"]

    def target(flags, at):
        return sum(v["effectiveBalance"]
                   for v, flag in zip(data["validators"], flags, strict=True)
                   if active(v, at) and not v["slashed"] and flag & 2)

    return {"total": sum(v["effectiveBalance"] for v in data["validators"] if active(v, epoch)),
            "previous": target(data["previousFlags"], max(0, epoch - 1)),
            "current": target(data["currentFlags"], epoch)}
