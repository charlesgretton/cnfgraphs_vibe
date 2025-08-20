// stuck_at_1_hard.c
// Harder CBMC benchmark: deep mixing logic with stuck-at-1 fault

#include <assert.h>
#include <stdint.h>

// CBMC nondeterministic input generators
uint32_t nondet_uint(void);

static uint32_t golden_logic(uint32_t x) {
    // 5-stage nonlinear mixing
    uint32_t s1 = (x ^ (x << 13)) + 0x9e3779b9;
    uint32_t s2 = (s1 ^ (s1 >> 17)) * 0x85ebca6b;
    uint32_t s3 = (s2 ^ (s2 << 5))  + 0xc2b2ae35;
    uint32_t s4 = (s3 ^ (s3 >> 11)) * 0x27d4eb2f;
    uint32_t s5 = (s4 ^ (s4 << 7))  + 0x165667b1;

    return s5;
}

static uint32_t faulty_logic(uint32_t x) {
    uint32_t s1 = (x ^ (x << 13)) + 0x9e3779b9;
    uint32_t s2 = (s1 ^ (s1 >> 17)) * 0x85ebca6b;

    // *** Inject stuck-at-1 fault here ***
    // Instead of using s2 as computed, force a single bit to be 1
    s2 |= (1u << 15); // stuck-at-1 on bit 15

    uint32_t s3 = (s2 ^ (s2 << 5))  + 0xc2b2ae35;
    uint32_t s4 = (s3 ^ (s3 >> 11)) * 0x27d4eb2f;
    uint32_t s5 = (s4 ^ (s4 << 7))  + 0x165667b1;

    return s5;
}

int main(void) {
    uint32_t x = nondet_uint();

    uint32_t y_golden = golden_logic(x);
    uint32_t y_faulty = faulty_logic(x);

    // If fault is detectable, some x will make outputs differ.
    assert(y_golden == y_faulty);

    return 0;
}
