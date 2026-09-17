#ifndef CL_ASM_ZISK_INPUT_H
#define CL_ASM_ZISK_INPUT_H

#include <stdbool.h>
#include <stdint.h>

enum { STATE_WORDS = 17, INPUT_WORDS = 21, ROOT_COUNT = 8192 };

static inline bool root_time_valid(uint64_t slot, uint64_t epoch) {
    const uint64_t start = epoch * 32;
    return start <= UINT64_MAX - ROOT_COUNT && start < slot &&
           slot - start <= ROOT_COUNT;
}

/* Match ClAsm.Weigh.ValidInput before calling the proved RV64 routine. */
static inline bool input_valid(const uint64_t input[INPUT_WORDS]) {
    if (input[1] >= 16 || input[17] > UINT64_MAX / 2 ||
        input[18] > UINT64_MAX / 3 || input[19] > UINT64_MAX / 3 ||
        input[2] > UINT64_MAX - 3 || input[7] > UINT64_MAX - 2) {
        return false;
    }
    const uint64_t epoch = input[0] / 32;
    const uint64_t previous = epoch == 0 ? 0 : epoch - 1;
    if (3 * input[18] >= 2 * input[17] && !root_time_valid(input[0], previous)) {
        return false;
    }
    return 3 * input[19] < 2 * input[17] || root_time_valid(input[0], epoch);
}

#endif
