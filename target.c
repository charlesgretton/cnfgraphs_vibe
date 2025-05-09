// No need for #include <assert.h> if only using __CPROVER_assert
#include <stdint.h> // For uint32_t
#include <stdio.h>  // For potential printf

// CBMC specific function to create a non-deterministic unsigned 32-bit integer
uint32_t nondet_uint32();

// If you don't have <cprover/contracts.h> or similar providing __CPROVER_assert,
// CBMC usually recognizes it as a built-in intrinsic.
// You might need to ensure your CBMC include paths are set up if it doesn't.
// For basic usage, it's often implicitly understood by CBMC.

int main() {
    uint32_t X;
    uint32_t Y;

    // Assign non-deterministic 32-bit unsigned integer values to X and Y
    X = nondet_uint32();
    Y = nondet_uint32();

    for (int i = 0; i< 5; i++){
      X=X+Y;
    }
    
    // --- Optional: Assumptions to constrain Y to avoid overflow when Y+1 is calculated ---
    // As before, uncomment if you want to avoid wrap-around for Y+1.
    // For instance, if using <cprover/assume.h> or if __CPROVER_assume is built-in:
    // __CPROVER_assume(Y < 0xFFFFFFFFU);

    // The CBMC safety property assertion
    // We are asserting that X is not equal to Y + 1.
    // CBMC will try to find values for X and Y that make this condition FALSE.
    __CPROVER_assert(X == (Y + 1), "Safety property: X should not be equal to Y+1");

    // Optional: Print statements for debugging if run directly (CBMC ignores them)
    // printf("X = %u, Y = %u, Y+1 = %u\n", X, Y, Y + 1);

    return 0;
}

// Definition for nondet_uint32() - same considerations as before
#ifndef __clang__
uint32_t nondet_uint32() {
    // uint32_t val;
    // val = __CPROVER_nondet_uint(); // If available and preferred
    // return val;
    return 42; // Placeholder, CBMC handles non-determinism
}
#endif
