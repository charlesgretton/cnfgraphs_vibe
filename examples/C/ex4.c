#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

// Standard CBMC built-in definitions
#ifndef __CPROVER_H_INCLUDED
#include <stdio.h>
uint32_t nondet_uint32_t() { static uint32_t val = 0; return val++; }
void __CPROVER_assume(int c) { if (!c) { /* In real code, might abort */ } }
#endif

#define NUM_ROUNDS 10
#define WORD_BITS 32

// A helper function for bitwise rotation.
uint32_t rotate_left(uint32_t value, int shift) {
    shift &= (WORD_BITS - 1);
    return (value << shift) | (value >> (WORD_BITS - shift));
}

/**
 * @brief A complex, non-linear bit-scrambling function (pseudo-hash).
 *
 * This function is designed to be difficult for a SAT solver to reverse or find
 * collisions for. It uses a mix of rotations, XORs, and additions with
 * data-dependent behavior.
 *
 * @param data The 32-bit data to be scrambled.
 * @param key  A 32-bit key to modify the scrambling.
 * @return The scrambled 32-bit result.
 */
uint32_t bit_scrambler(uint32_t data, uint32_t key) {
    uint32_t round_constant = 0x9E3779B9; // A value from the TEA algorithm

    for (int i = 0; i < NUM_ROUNDS; ++i) {
        data += ((key << 4) ^ (key >> 5)) + key;
        key += ((data << 4) ^ (data >> 5)) + data + round_constant;
        data = rotate_left(data, (key & 0x1F)); // Data-dependent rotation
        key ^= 0xDEADBEEF;
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
 *        is found between two different inputs.
 *
 * The fault condition itself is what is hard to find.
 */
uint32_t faulty_circuit(uint32_t input_a, uint32_t key_a, uint32_t input_b, uint32_t key_b) {
    // 1. Compute the scrambled versions of both inputs.
    uint32_t scrambled_a = bit_scrambler(input_a, key_a);
    uint32_t scrambled_b = bit_scrambler(input_b, key_b);

    // 2. Define the fault trigger condition: a non-trivial collision.
    //    This is the computationally hard part for CBMC to satisfy.
    //    It must find two different inputs that produce the same scrambled output.
    bool fault_trigger = (input_a != input_b) && (scrambled_a == scrambled_b);

    // 3. Inject the fault if the trigger condition is met.
    uint32_t final_output = scrambled_a;
    if (fault_trigger) {
        // The fault is a simple, direct corruption of the output.
        // It CANNOT be masked. If the trigger is found, the output WILL be different.
        final_output ^= 0xFFFFFFFF; // Flip all the bits
    }

    return final_output;
}


int main() {
    // 1. Create a large, non-deterministic input space.
    // We need two distinct inputs to search for a collision.
    uint32_t input_a = nondet_uint32_t();
    uint32_t key_a   = nondet_uint32_t();
    uint32_t input_b = nondet_uint32_t();
    uint32_t key_b   = nondet_uint32_t();

    // 2. Add a crucial assumption to look for a non-trivial collision.
    // This prevents the solver from taking the trivial shortcut of setting
    // input_a == input_b.
    __CPROVER_assume(input_a != input_b);

    // 3. Simulate both circuits.
    uint32_t out_good   = good_circuit(input_a, key_a);
    uint32_t out_faulty = faulty_circuit(input_a, key_a, input_b, key_b);

    // 4. Assert that the outputs are always equal.
    // CBMC will now spend a significant amount of time trying to solve the
    // complex system of equations to make `scrambled_a == scrambled_b`
    // with `input_a != input_b`. When it succeeds, the assertion will fail.
    assert(out_good == out_faulty);

    return 0;
}
