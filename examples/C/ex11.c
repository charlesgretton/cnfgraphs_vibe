#include <assert.h>
#include <stdint.h>

uint32_t nondet_uint(void);

uint32_t modexp(uint32_t base, uint32_t exp, uint32_t mod) {
  uint64_t res = 1;
  uint64_t b = base % mod;
  while (exp > 0) {
    if (exp & 1) res = (res * b) % mod;
    b = (b * b) % mod;
    exp >>= 1;
  }
  return (uint32_t)res;
}

int main(void) {
  uint32_t x = nondet_uint();
  uint32_t g = modexp(x, 17, 2579);    // "golden"
  uint32_t f = (g | (1u << 5));        // stuck-at fault on bit 5 of result
  assert(g == f);
}
