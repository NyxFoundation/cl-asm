"""Extract the exact pinned reference definitions used by the differential oracle."""

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re


REVISION = "530cf56a3920dc048900b4b7a408b3acd71331fa"
PHASE0_SOURCE_SHA256 = "95bbeca116dfc60ee75c1713d32409e29854de2340a71ee325ff7257f4412483"
ALTAIR_SOURCE_SHA256 = "ca044221f5d2282f272de5844d07189c1ddacbce7ba27621a87464fa90322f5c"
WEIGH_NAMES = ["Epoch", "Slot", "Gwei", "Root", "BlockRoots", "JustificationBits", "Checkpoint",
               "compute_epoch_at_slot", "compute_start_slot_at_epoch",
               "get_current_epoch", "get_previous_epoch", "get_block_root",
               "get_block_root_at_slot", "weigh_justification_and_finalization"]
PHASE0_BALANCE_NAMES = ["compute_epoch_at_slot", "get_current_epoch", "get_previous_epoch",
                        "is_active_validator", "get_active_validator_indices",
                        "get_total_balance", "get_total_active_balance"]
ALTAIR_BALANCE_NAMES = ["has_flag", "get_unslashed_participating_indices"]
ROOT = Path(__file__).resolve().parents[1]


def extract(source: str, names: list[str], preamble: bool = True) -> str:
    found = {}
    for block in re.findall(r"```python\n(.*?)```", source, re.DOTALL):
        for node in ast.parse(block).body:
            if isinstance(node, (ast.FunctionDef, ast.ClassDef)) and node.name in names:
                if node.name in found:
                    raise ValueError(f"duplicate reference definition: {node.name}")
                found[node.name] = ast.get_source_segment(block, node)
    if set(found) != set(names):
        raise ValueError("missing reference definitions")
    if not preamble:
        return "\n\n\n".join(found[n] for n in names) + "\n"
    header = f'"""Unmodified definitions from ethereum/consensus-specs {REVISION}; CC0-1.0."""\n'
    return header + "from __future__ import annotations\n\n\n" + \
        "\n\n\n".join(found[n] for n in names) + "\n"


def write_vendored(destination: Path, name: str, extracted: str) -> str:
    (destination / name).write_text(extracted)
    return hashlib.sha256(extracted.encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="pinned specs/phase0/beacon-chain.md")
    parser.add_argument("--altair", type=Path, default=None,
                        help="pinned specs/altair/beacon-chain.md; enables the balance extraction")
    parser.add_argument("--altair-sha256", default=ALTAIR_SOURCE_SHA256,
                        help="expected sha256 of the altair source")
    args = parser.parse_args()
    source = args.source.read_bytes()
    if hashlib.sha256(source).hexdigest() != PHASE0_SOURCE_SHA256:
        raise ValueError("source does not match the pinned consensus specification")
    destination = ROOT / "tests/vendor"
    destination.mkdir(exist_ok=True)
    extracted_weigh = extract(source.decode(), WEIGH_NAMES)
    metadata = {"revision": REVISION, "path": "specs/phase0/beacon-chain.md",
                "source_sha256": hashlib.sha256(source).hexdigest(),
                "extracted_sha256": write_vendored(destination, "phase0_weigh.py", extracted_weigh),
                "definitions": WEIGH_NAMES, "ssz_package": "eth-ssz-specs==0.1.0"}
    if args.altair is not None:
        altair_source = args.altair.read_bytes()
        if hashlib.sha256(altair_source).hexdigest() != args.altair_sha256:
            raise ValueError("altair source does not match the pinned consensus specification")
        balances = (extract(source.decode(), PHASE0_BALANCE_NAMES) +
                    "\n\n" + extract(altair_source.decode(), ALTAIR_BALANCE_NAMES, preamble=False))
        phase0_head = hashlib.sha256(balances.encode()).hexdigest()
        metadata["aggregation"] = {
            "extracted_sha256": write_vendored(destination, "aggregate_balances.py", balances),
            "sources": [
                {"path": "specs/phase0/beacon-chain.md",
                 "source_sha256": PHASE0_SOURCE_SHA256, "definitions": PHASE0_BALANCE_NAMES},
                {"path": "specs/altair/beacon-chain.md",
                 "source_sha256": hashlib.sha256(altair_source).hexdigest(),
                 "definitions": ALTAIR_BALANCE_NAMES},
            ],
        }
    (destination / "reference.json").write_text(json.dumps(metadata, indent=2) + "\n")


if __name__ == "__main__":
    main()
