import json
import unittest

from test_weigh import ELF, RUNNER
from weigh_cases import make_case
from official_oracle import evaluate
import subprocess


class BenchmarkTests(unittest.TestCase):
    def test_should_measure_checked_execution_with_observable_checksum(self):
        data = make_case()
        output = subprocess.run([str(RUNNER), str(ELF), "--benchmark", "2", "2"],
            input=json.dumps(data) + "\n", text=True, capture_output=True, check=True)
        report = json.loads(output.stdout)
        result = report["result"]
        steps = result.pop("steps")
        self.assertEqual(result, evaluate(data))
        self.assertEqual(report["iterationsPerBatch"], 2)
        self.assertEqual(len(report["batchNanoseconds"]), 2)
        self.assertTrue(all(value > 0 for value in report["batchNanoseconds"]))
        self.assertEqual(report["checksum"], 4 * (steps + result["bits"]))

    def test_should_reject_invalid_benchmark_counts(self):
        output = subprocess.run([str(RUNNER), str(ELF), "--benchmark", "0", "2"],
            input=json.dumps(make_case()) + "\n", text=True, capture_output=True, check=False)
        self.assertNotEqual(output.returncode, 0)
        self.assertIn("invalid benchmark", output.stderr)
