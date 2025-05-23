// No need for #include <assert.h> if only using __CPROVER_assert
#include <stdint.h> // For uint32_t
#include <stdio.h>  // For potential printf

// CBMC specific function to create a non-deterministic unsigned 32-bit integer
uint8_t nondet_uint8();

// If you don't have <cprover/contracts.h> or similar providing __CPROVER_assert,
// CBMC usually recognizes it as a built-in intrinsic.
// You might need to ensure your CBMC include paths are set up if it doesn't.
// For basic usage, it's often implicitly understood by CBMC.

int main() {
  
  uint8_t N = 2;
  uint8_t branches[N];
  
  for (uint8_t i = 0; i< N; i++){
    branches[i] = nondet_uint8();
    __CPROVER_assume(branches[i] >= 0);
    __CPROVER_assume(branches[i] < 10);
  }  
    
  uint8_t numbers[N];
  for (uint8_t i = 0; i< N; i++){
    numbers[i] = nondet_uint8();
    __CPROVER_assume(numbers[i] > 0);
    __CPROVER_assume(numbers[i] < 10);
  }


  
  
  uint8_t index = 0;
  if (0 == branches[index]){
    while (index < N-1){
      numbers[index+1] = numbers[index]+1;
      index++;
    }
    __CPROVER_assert(numbers[0] == numbers[N-1], "Reachable Safety property 2.");
  } else if (1 == branches[index]){
    while (index < N-1){
      numbers[index+1] = numbers[index];
      index++;
    }
    __CPROVER_assert(numbers[0] == numbers[N-1], "Reachable Safety property 1.");
  }


  return 0;
}
