// hard_smallcnf.c
#include <assert.h>
#include <stdint.h>

uint32_t nondet_uint(void);

// Compute parity of n bits recursively.
// This builds a *logarithmic depth* circuit with a small CNF footprint
// but makes the SAT solver branch heavily to find a counterexample.
uint32_t parity(uint32_t x, int n) {
  if (n == 0) return 0;
  if (n == 1) return x & 1u;
  int mid = n / 2;
  return parity(x >> mid, n - mid) ^ parity(x, mid);
}

int main(void) {
  uint32_t x = nondet_uint();

  // Golden: true parity
  uint32_t g = parity(x, 32);

  // Faulty: stuck-at-1 on one bit of input
  uint32_t xf = x | (1u << 7);
  uint32_t f = parity(xf, 32);

  // If they ever differ, CBMC should find it.
  assert(g == f);
}
