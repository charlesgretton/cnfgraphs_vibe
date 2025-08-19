#include <assert.h>
#include <stdbool.h>

// To make the code compatible with standard C compilers for testing,
// we can define the CBMC built-ins when not using CBMC.
#ifndef __CPROVER_H_INCLUDED
#include <stdio.h>
int nondet_int();
void __CPROVER_assume(int condition) { 
    // In a regular compilation, this does nothing.
    // In CBMC, it adds a constraint.
}
#endif

/**
 * @brief Implements the fault-free ("good") version of the circuit.
 * 
 * Logic: output = (a AND b) XOR c
 */
bool good_circuit(bool a, bool b, bool c) {
    bool wire1 = a && b; // The intermediate wire
    bool output = wire1 ^ c;
    return output;
}

/**
 * @brief Implements the faulty version of the circuit.
 * 
 * A "Stuck-at-1" fault is injected on the wire carrying the result of (a AND b).
 * This means `wire1` is always forced to be true (1), regardless of inputs a and b.
 */
bool faulty_circuit(bool a, bool b, bool c) {
    bool wire1 = a && b;
    
    // FAULT INJECTION: The wire is "stuck" at a high signal (true).
    wire1 = true; 

    bool output = wire1 ^ c;
    return output;
}

/**
 * @brief The main function acts as a "test harness" for CBMC.
 * 
 * CBMC will try to find a set of inputs (a, b, c) that cause the assertion to fail.
 * A failed assertion means we have found a test pattern that distinguishes the
 * good circuit from the faulty one.
 */
int main() {
    // 1. Create non-deterministic inputs. These are the primary inputs
    //    of the circuit that CBMC will try to assign values to.
    bool a = nondet_int();
    bool b = nondet_int();
    bool c = nondet_int();

    // Note: We don't need __CPROVER_assume here because C's `bool` type,
    // when generated from `nondet_int()`, is already constrained by CBMC 
    // to be either 0 or 1.

    // 2. Simulate both the good and the faulty circuit with the same inputs.
    bool out_good = good_circuit(a, b, c);
    bool out_faulty = faulty_circuit(a, b, c);

    // 3. Assert that the outputs are always equal.
    //    If CBMC finds a counterexample, it means it found a set of inputs
    //    (a, b, c) where out_good != out_faulty. This set of inputs is
    //    our desired "test pattern" that reveals the fault.
    assert(out_good == out_faulty);

    return 0;
}
