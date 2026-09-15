"""Deterministic, admitted whole-routine cases and named benchmark scenarios."""

import random


MAX_WORD = 2**64 - 1


def make_case(slot=257, bits=7, previous_epoch=5, current_epoch=7,
              previous_balance=64, current_balance=64, total=96, seed=0x1122334455667788):
    return {"slot": slot, "bits": bits, "total": total,
            "previousBalance": previous_balance, "currentBalance": current_balance,
            "rootSeed": seed,
            "previous": {"epoch": previous_epoch, "root": [11, 22, 33, 44]},
            "current": {"epoch": current_epoch, "root": [55, 66, 77, 88]},
            "finalized": {"epoch": 0, "root": [99, 111, 222, 333]}}


def cases():
    result = []
    epochs = [0, 1, 2, 3, 8, 255, 256, 257, 511, 512]
    relations = [(3, 3), (2, 3), (4, 2), (4, 1), (3, 2), (2, 1), (0, 0)]
    for epoch in epochs:
        for bits in range(16):
            for previous_balance, current_balance in [(63, 63), (64, 63), (63, 64), (64, 64)]:
                for previous_delta, current_delta in relations:
                    result.append(make_case(epoch * 32 + 1, bits,
                        max(epoch - previous_delta, 0), max(epoch - current_delta, 0),
                        previous_balance, current_balance))
    for total in [0, 1, 2, 3, 96, 2**32, 2**62, MAX_WORD // 2]:
        for vote in [0, 1, max(2 * total // 3 - 1, 0), 2 * total // 3,
                     2 * total // 3 + 1, MAX_WORD // 3]:
            if vote * 3 <= MAX_WORD:
                result.append(make_case(previous_balance=vote, current_balance=vote, total=total))
    for slot in [0, 31, 32, 33, 8191, 8192, 8193, 2**32, 2**63, MAX_WORD - 8192, MAX_WORD]:
        result.append(make_case(slot=slot, previous_balance=0, current_balance=0))
    result.append(make_case(previous_epoch=MAX_WORD - 3, current_epoch=MAX_WORD - 2))
    randomizer = random.Random(530)
    for _ in range(256):
        epoch = randomizer.randrange(2**50)
        result.append(make_case(epoch * 32 + randomizer.randrange(1, 32), randomizer.randrange(16),
            max(epoch - randomizer.randrange(5), 0), max(epoch - randomizer.randrange(5), 0),
            randomizer.randrange(96), randomizer.randrange(96), seed=randomizer.randrange(4)))
    return result


def benchmark_cases():
    return {
        "no-updates": make_case(bits=0, previous_balance=0, current_balance=0),
        "previous-only": make_case(bits=0, previous_balance=64, current_balance=0),
        "current-only": make_case(bits=0, previous_balance=0, current_balance=64),
        "both-justified": make_case(bits=0, previous_balance=64, current_balance=64, current_epoch=8),
        "two-finalizations": make_case(bits=7, previous_epoch=6, current_epoch=7),
        "genesis-shared-root": make_case(slot=1, bits=0, previous_epoch=0, current_epoch=0),
    }
