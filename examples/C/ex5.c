#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

// Standard CBMC built-in definitions
#ifndef __CPROVER_H_INCLUDED
uint32_t nondet_uint32_t() {
    static uint32_t val = 0;
    return val++;
}
void __CPROVER_assume(int c) {
    if (!c) {
        /* In real code, might abort */
    }
}
#endif

// REDUCED ROUNDS: This is the key to making collisions findable.
#define NUM_ROUNDS 5
#define WORD_BITS 32

// A helper function for bitwise rotation.
uint32_t rotate_left(uint32_t value, int shift) {
    shift &= (WORD_BITS - 1);
    return (value << shift) | (value >> (WORD_BITS - shift));
}

/**
 * @brief A WEAKER, non-linear bit-scrambling function.
 *
 * With fewer rounds and simpler logic, this function is guaranteed to have
 * many collisions that a SAT solver can find after significant effort.
 *
 * @param data The 32-bit data to be scrambled.
 * @param key A 32-bit key to modify the scrambling.
 * @return The scrambled 32-bit result.
 */
uint32_t bit_scrambler(uint32_t data, uint32_t key) {
    uint32_t round_constant = 0x9E3779B9;
    for (int i = 0; i < NUM_ROUNDS; ++i) {
        // Simplified logic compared to previous versions
        data = rotate_left(data, 7) ^ key;
        data += round_constant;
        key -= data;
    }
    return data;
}

/**
 * @brief The good circuit's behavior. It simply scrambles an input.
 */
uint32_t good_circuit(uint32_t input_a, uint32_t key_a) {
    return bit_scrambler(input_a, key_a);
}

/**
 * @brief The faulty circuit. A fault is injected ONLY if a hash collision
 * is found between two different inputs.
 */
uint32_t faulty_circuit(uint32_t input_a, uint32_t key_a, uint32_t input_b, uint32_t key_b) {
    uint32_t scrambled_a = bit_scrambler(input_a, key_a);
    uint32_t scrambled_b = bit_scrambler(input_b, key_b);

    // The fault trigger condition: a non-trivial collision.
    bool fault_trigger = (input_a != input_b) && (scrambled_a == scrambled_b);
    uint32_t final_output = scrambled_a;

    if (fault_trigger) {
        // The fault is a simple, direct corruption that cannot be masked.
        final_output ^= 0xDEADBEEF;
    }

    return final_output;
}

int main() {
    // 1. Create two distinct non-deterministic inputs to search for a collision.
    uint32_t input_a = nondet_uint32_t();
    uint32_t key_a = nondet_uint32_t();
    uint32_t input_b = nondet_uint32_t();
    uint32_t key_b = nondet_uint32_t();

    // 2. Assume the primary inputs are different.
    __CPROVER_assume(input_a != input_b);

    // 3. Simulate both circuits.
    uint32_t out_good = good_circuit(input_a, key_a);
    uint32_t out_faulty = faulty_circuit(input_a, key_a, input_b, key_b);

    // 4. Assert that the outputs are always equal.
    // This will now fail, because the weaker scrambler allows CBMC to satisfy
    // the `fault_trigger` condition.
    assert(out_good == out_faulty);

    return 0;
}
