#include <assert.h>
#include <stdbool.h>
#include <stdint.h> // For fixed-width integers like uint8_t

// To make the code compatible with standard C compilers for testing,
// we can define the CBMC built-ins when not using CBMC.
#ifndef __CPROVER_H_INCLUDED
#include <stdio.h>
// These are simple stand-ins for non-CBMC compilation
unsigned char nondet_uint8_t() { static unsigned char val = 0; return val++; }
void __CPROVER_assume(int c) { if (!c) { /* In real code, might abort */ } }
#endif

// Define the bit-width of our ALU's operands
#define NUM_BITS 8

/**
 * @brief Implements the fault-free ("good") version of a simple 8-bit ALU.
 *
 * This ALU supports four operations based on the opcode:
 *   - 0: Addition (a + b)
 *   - 1: Bitwise AND (a & b)
 *   - 2: Multiplication (a * b)
 *   - 3: Logical Shift Right (a >> (b % 8))
 *
 * The multiplication is implemented with an explicit shift-and-add algorithm
 * to create intermediate "wires" (variables) where a fault can be injected.
 * 
 * @param a The first 8-bit operand.
 * @param b The second 8-bit operand.
 * @param opcode A 2-bit value selecting the operation.
 * @return A 16-bit result.
 */
uint16_t good_circuit(uint8_t a, uint8_t b, uint8_t opcode) {
    uint16_t result = 0;

    switch (opcode) {
        case 0: // ADD
            result = (uint16_t)a + (uint16_t)b;
            break;

        case 1: // AND
            result = (uint16_t)a & (uint16_t)b;
            break;

        case 2: // MULTIPLY (Shift-and-add implementation)
        {
            uint16_t product_accumulator = 0;
            uint16_t shifted_a = a;

            for (int i = 0; i < NUM_BITS; ++i) {
                // If the i-th bit of b is 1, add the shifted 'a' to the result.
                if ((b >> i) & 1) {
                    product_accumulator += (shifted_a << i);
                }
            }
            result = product_accumulator;
            break;
        }

        case 3: // SHIFT RIGHT
            // Use only lower 3 bits of b to ensure shift amount is within [0, 7]
            result = (uint16_t)a >> (b & 0x7);
            break;
        
        default:
            // Behavior for other opcodes is undefined.
            // We will use __CPROVER_assume to prevent CBMC from exploring this.
            break;
    }
    return result;
}

/**
 * @brief Implements the faulty version of the ALU.
 *
 * A "Stuck-at-1" fault is injected on an intermediate wire inside the
 * multiplication logic. Specifically, after the 3rd iteration (i=2) of the
 * shift-and-add loop, bit 5 of the `product_accumulator` is forced to 1.
 * This is a subtle fault that only manifests under specific conditions.
 */
uint16_t faulty_circuit(uint8_t a, uint8_t b, uint8_t opcode) {
    uint16_t result = 0;

    switch (opcode) {
        case 0: // ADD (unaffected)
            result = (uint16_t)a + (uint16_t)b;
            break;

        case 1: // AND (unaffected)
            result = (uint16_t)a & (uint16_t)b;
            break;

        case 2: // MULTIPLY (fault location)
        {
            uint16_t product_accumulator = 0;
            uint16_t shifted_a = a;

            for (int i = 0; i < NUM_BITS; ++i) {
                if ((b >> i) & 1) {
                    product_accumulator += (shifted_a << i);
                }
                
                // --- FAULT INJECTION ---
                // After the addition for the 3rd bit of 'b' is complete (i=2),
                // we simulate that bit 5 of the internal accumulator bus gets
                // stuck at a high signal (1).
                if (i == 2) {
                    // This is our intermediate "wire" or bus.
                    // Force its 5th bit to 1. (1 << 5 is 32 or 0x20)
                    product_accumulator = product_accumulator | (1 << 5);
                }
            }
            result = product_accumulator;
            break;
        }

        case 3: // SHIFT RIGHT (unaffected)
            result = (uint16_t)a >> (b & 0x7);
            break;
            
        default:
            break;
    }
    return result;
}

/**
 * @brief The main function acts as a "test harness" for CBMC.
 *
 * CBMC will explore the state space of non-deterministic inputs (a, b, opcode)
 * to find a combination that causes the assertion to fail. A failed assertion
 * proves that there exists a test vector that can distinguish the good circuit
 * from the faulty one.
 */
int main() {
    // 1. Create non-deterministic inputs for the ALU.
    uint8_t a = nondet_uint8_t();
    uint8_t b = nondet_uint8_t();
    uint8_t opcode = nondet_uint8_t();

    // 2. Constrain the inputs to valid values. The opcode is only 2 bits wide,
    //    so it can only be 0, 1, 2, or 3. This assumption focuses CBMC's
    //    search on the defined behavior of our circuit.
    __CPROVER_assume(opcode >= 0 && opcode <= 3);

    // 3. Simulate both the good and the faulty circuit with the same inputs.
    uint16_t out_good = good_circuit(a, b, opcode);
    uint16_t out_faulty = faulty_circuit(a, b, opcode);

    // 4. Assert that the outputs are always equal.
    //    If CBMC finds a counterexample, it has found a test pattern (a, b, opcode)
    //    that reveals the stuck-at-1 fault.
    assert(out_good == out_faulty);

    return 0;
}
