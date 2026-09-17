#include "input.h"

/* ZisK v1.2.0-alpha: ziskos/entrypoint and core/src/mem.rs. */
#define INPUT_RECORD ((const volatile uint64_t *)UINT64_C(0x40000008))
#define PUBLIC_OUTPUT ((volatile uint32_t *)UINT64_C(0xa0410000))

static uint64_t state[STATE_WORDS];
static uint64_t roots[ROOT_COUNT][4];
static uint64_t scratch[10];

extern void weigh(uint64_t *, const uint64_t (*)[4], uint64_t, uint64_t,
                  uint64_t, uint64_t *);

/* The input-ready hint only loads bytes; all input values are public outputs. */
static void input_ready(uint64_t last_address) {
    __asm__ volatile("csrs 0x8f0, %0\n\tcsrwi 0x8c0, 23"
                     : : "r"(last_address) : "memory");
}

static void initialize(const uint64_t input[INPUT_WORDS]) {
    for (unsigned i = 0; i < STATE_WORDS; ++i) {
        state[i] = input[i];
    }
    for (uint64_t i = 0; i < ROOT_COUNT; ++i) {
        roots[i][0] = input[20];
        roots[i][1] = i;
        roots[i][2] = input[20] ^ i;
        roots[i][3] = UINT64_C(0x1020304050607080) + i;
    }
    for (unsigned i = 0; i < 10; ++i) {
        scratch[i] = 0;
    }
}

static bool preserved(const uint64_t input[INPUT_WORDS]) {
    if (state[0] != input[0]) {
        return false;
    }
    for (unsigned i = 0; i < 5; ++i) {
        if (state[2 + i] != input[7 + i] || scratch[i] != input[2 + i] ||
            scratch[5 + i] != input[7 + i]) {
            return false;
        }
    }
    return true;
}

static void output_word(unsigned index, uint64_t value) {
    PUBLIC_OUTPUT[index] = (uint32_t)value;
    PUBLIC_OUTPUT[index + 1] = (uint32_t)(value >> 32);
}

static void commit(const uint64_t input[INPUT_WORDS]) {
    for (unsigned i = 0; i < INPUT_WORDS; ++i) {
        output_word(1 + 2 * i, input[i]);
    }
    PUBLIC_OUTPUT[43] = (uint32_t)state[1];
    for (unsigned i = 0; i < 10; ++i) {
        output_word(44 + 2 * i, state[7 + i]);
    }
    PUBLIC_OUTPUT[0] = 1;
}

int guest_main(void) {
    uint64_t input[INPUT_WORDS];
    PUBLIC_OUTPUT[0] = 0;
    input_ready(UINT64_C(0x4000000f));
    if (INPUT_RECORD[0] != INPUT_WORDS * sizeof(uint64_t)) {
        return 1;
    }
    input_ready(UINT64_C(0x40000010) + sizeof(input) - 1);
    for (unsigned i = 0; i < INPUT_WORDS; ++i) {
        input[i] = INPUT_RECORD[1 + i];
    }
    if (!input_valid(input)) {
        return 2;
    }
    initialize(input);
    weigh(state, roots, input[17], input[18], input[19], scratch);
    if (!preserved(input)) {
        return 3;
    }
    commit(input);
    return 0;
}
