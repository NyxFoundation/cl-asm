"""Deterministic aggregation inputs spanning eligibility, flags, and sum boundaries."""

import random

MAX_WORD = 2**64 - 1
INCREMENT = 10**9


def validator(balance=32 * INCREMENT, activation=0, exit_epoch=MAX_WORD, slashed=0):
    return {"effectiveBalance": balance, "activationEpoch": activation,
            "exitEpoch": exit_epoch, "slashed": slashed}


def make_case(validators=None, previous=None, current=None, slot=96):
    values = [validator()] if validators is None else validators
    return {"slot": slot, "validators": values,
            "previousFlags": [2] * len(values) if previous is None else previous,
            "currentFlags": [2] * len(values) if current is None else current}


def cases():
    values = [make_case([])]
    for slot in [0, 1, 31, 32, 63, 64, 95, 96, MAX_WORD]:
        epoch = slot // 32
        for balance in [0, INCREMENT - 1, INCREMENT, INCREMENT + 1, MAX_WORD]:
            values.append(make_case([validator(balance)], slot=slot))
        for activation in [0, max(0, epoch - 1), epoch, epoch + 1]:
            for exit_epoch in [0, epoch, epoch + 1, MAX_WORD]:
                for slashed in [0, 1]:
                    values.append(make_case(
                        [validator(32 * INCREMENT, activation, exit_epoch, slashed)], slot=slot))
    for flag in range(256):
        values.append(make_case(previous=[flag], current=[flag ^ 255]))
    values.extend([
        make_case([validator(MAX_WORD - 1), validator(1)]),
        make_case([validator(MAX_WORD), validator(MAX_WORD, activation=4)]),
        make_case([validator(INCREMENT, activation=3), validator(INCREMENT, exit_epoch=3)]),
    ])
    rng = random.Random(530)
    for _ in range(200):
        epoch = rng.randrange(0, 30)
        count = rng.randrange(0, 65)
        validators = [validator(rng.randrange(0, 65) * INCREMENT,
                      rng.randrange(0, 35), rng.randrange(0, 40), rng.randrange(2))
                      for _ in range(count)]
        values.append(make_case(validators, [rng.randrange(256) for _ in validators],
                                [rng.randrange(256) for _ in validators],
                                epoch * 32 + rng.randrange(32)))
    return values
