"""Extract the exact pinned Phase0 functions used by the differential oracle."""

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re


REVISION = "530cf56a3920dc048900b4b7a408b3acd71331fa"
SOURCE_SHA256 = "95bbeca116dfc60ee75c1713d32409e29854de2340a71ee325ff7257f4412483"
NAMES = ["Epoch", "Slot", "Gwei", "Root", "BlockRoots", "JustificationBits", "Checkpoint",
         "compute_epoch_at_slot", "compute_start_slot_at_epoch",
         "get_current_epoch", "get_previous_epoch", "get_block_root",
         "get_block_root_at_slot", "weigh_justification_and_finalization"]
ROOT = Path(__file__).resolve().parents[1]


def extract(source: str) -> str:
    found = {}
    for block in re.findall(r"```python\n(.*?)```", source, re.DOTALL):
        for node in ast.parse(block).body:
            if isinstance(node, (ast.FunctionDef, ast.ClassDef)) and node.name in NAMES:
                if node.name in found:
                    raise ValueError(f"duplicate reference definition: {node.name}")
                found[node.name] = ast.get_source_segment(block, node)
    if set(found) != set(NAMES):
        raise ValueError("missing reference definitions")
    header = f'"""Unmodified definitions from ethereum/consensus-specs {REVISION}; CC0-1.0."""\n'
    return header + "from __future__ import annotations\n\n\n" + "\n\n\n".join(found[n] for n in NAMES) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="pinned specs/phase0/beacon-chain.md")
    args = parser.parse_args()
    source = args.source.read_bytes()
    if hashlib.sha256(source).hexdigest() != SOURCE_SHA256:
        raise ValueError("source does not match the pinned consensus specification")
    destination = ROOT / "tests/vendor"
    destination.mkdir(exist_ok=True)
    extracted = extract(source.decode())
    (destination / "phase0_weigh.py").write_text(extracted)
    metadata = {"revision": REVISION, "path": "specs/phase0/beacon-chain.md",
                "source_sha256": hashlib.sha256(source).hexdigest(),
                "extracted_sha256": hashlib.sha256(extracted.encode()).hexdigest(),
                "definitions": NAMES, "ssz_package": "eth-ssz-specs==0.1.0"}
    (destination / "reference.json").write_text(json.dumps(metadata, indent=2) + "\n")


if __name__ == "__main__":
    main()
