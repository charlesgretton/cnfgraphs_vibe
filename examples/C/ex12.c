#include <assert.h>
#include <stdint.h>

uint32_t nondet_uint(void);

uint32_t big_xor(uint32_t x) {
  uint32_t acc = 0;
  for (int i = 0; i < 32; ++i) {
    acc ^= (x >> i) & 1u;
  }
  return acc;
}

int main(void) {
  uint32_t x = nondet_uint();
  uint32_t g = big_xor(x);
  uint32_t f = big_xor(x | (1u << 15)); // stuck-at-1 fault on bit 15
  assert(g == f);
}
