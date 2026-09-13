"""Run unmodified pinned reference definitions with their actual SSZ types."""

from functools import lru_cache
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import struct
import sys
from types import ModuleType, SimpleNamespace

from ssz import BitVector, Boolean, ByteVector, Container, Uint64, Vector


class Bytes32(ByteVector):
    LENGTH = 32


def load_reference() -> ModuleType:
    if version("eth-ssz-specs") != "0.1.0":
        raise RuntimeError("the oracle requires eth-ssz-specs==0.1.0")
    directory = Path(__file__).parent / "vendor"
    metadata = json.loads((directory / "reference.json").read_text())
    source = (directory / "phase0_weigh.py").read_bytes()
    if hashlib.sha256(source).hexdigest() != metadata["extracted_sha256"]:
        raise RuntimeError("reference source hash mismatch")
    module = ModuleType("cl_asm_pinned_phase0")
    module.__dict__.update(Container=Container, Uint64=Uint64, Bytes32=Bytes32,
                           BitVector=BitVector, Boolean=Boolean, Vector=Vector,
                           SLOTS_PER_EPOCH=32, SLOTS_PER_HISTORICAL_ROOT=8192,
                           JUSTIFICATION_BITS_LENGTH=4, GENESIS_EPOCH=Uint64(0))
    sys.modules[module.__name__] = module
    exec(compile(source, str(directory / "phase0_weigh.py"), "exec"), module.__dict__)
    module.GENESIS_EPOCH = module.Epoch(0)
    return module


REFERENCE = load_reference()


@lru_cache(maxsize=8)
def roots(seed: int):
    return REFERENCE.BlockRoots(data=[REFERENCE.Root(struct.pack(
        "<QQQQ", seed, i, seed ^ i, 0x1020304050607080 + i)) for i in range(8192)])


def checkpoint(data: dict):
    return REFERENCE.Checkpoint(epoch=REFERENCE.Epoch(data["epoch"]),
                                root=REFERENCE.Root(struct.pack("<QQQQ", *data["root"])))


def prepare(data: dict):
    return SimpleNamespace(
        slot=REFERENCE.Slot(data["slot"]),
        justification_bits=REFERENCE.JustificationBits(
            data=[Boolean(bool(data["bits"] & (1 << i))) for i in range(4)]),
        previous_justified_checkpoint=checkpoint(data["previous"]),
        current_justified_checkpoint=checkpoint(data["current"]),
        finalized_checkpoint=checkpoint(data["finalized"]),
        block_roots=roots(data["rootSeed"]),
    )


def encode_checkpoint(value) -> dict:
    return {"epoch": int(value.epoch), "root": list(struct.unpack("<QQQQ", value.root))}


def evaluate(data: dict) -> dict:
    state = prepare(data)
    REFERENCE.weigh_justification_and_finalization(
        state, REFERENCE.Gwei(data["total"]), REFERENCE.Gwei(data["previousBalance"]),
        REFERENCE.Gwei(data["currentBalance"]))
    return {"slot": int(state.slot),
            "bits": sum(int(bit) << i for i, bit in enumerate(state.justification_bits)),
            "previous": encode_checkpoint(state.previous_justified_checkpoint),
            "current": encode_checkpoint(state.current_justified_checkpoint),
            "finalized": encode_checkpoint(state.finalized_checkpoint)}
