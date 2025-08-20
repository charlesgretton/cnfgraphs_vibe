// cbmc_stuck_at1_lowram.c
// Goal: hard-for-time, modest-for-RAM CBMC instance.
// Small 32-bit Feistel network, many rounds, internal stuck-at-1 fault.

#include <assert.h>
#include <stdint.h>

// ---- Tunables (adjust to push runtime without big memory) ----
#ifndef ROUNDS
#define ROUNDS 4096       // Increase to make it slower; RAM grows ~linearly but small per round
#endif

#ifndef FAULT_ROUND
#define FAULT_ROUND (ROUNDS - 64) // inject late so effect propagates
#endif

#ifndef FAULT_BIT
#define FAULT_BIT 7       // bit within f(x) to force to 1
#endif
// --------------------------------------------------------------

// CBMC nondeterministic inputs
uint16_t nondet_uint16_t(void);

// Cheap 16-bit rotate-left without UB
static inline uint16_t rotl16(uint16_t x, unsigned r) {
  r &= 15u;
  return (uint16_t)((x << r) | (x >> ((16u - r) & 15u)));
}

// Nonlinear round function on 16 bits (ARX-ish with bit-mixing).
static inline uint16_t f(uint16_t x, uint16_t k) {
  // Mix with key, then a few nonlinear layers.
  uint16_t a = x ^ k;
  uint16_t b = (uint16_t)(a + rotl16(a, 3));
  uint16_t c = (uint16_t)(b ^ rotl16(b, 6));
  uint16_t d = (uint16_t)(c + rotl16(c, (unsigned)(a & 15u)));
  // Small S-box-ish nibble shuffle to add nonlinearity but keep footprint low.
  uint16_t t = (uint16_t)(((d & 0x1111u) << 3) ^ ((d & 0x2222u) >> 1)
                        ^ ((d & 0x4444u) >> 2) ^ ((d & 0x8888u) >> 3));
  return (uint16_t)(d ^ t);
}

// Faulty version of f() with stuck-at-1 on one internal bit near FAULT_ROUND.
// We keep the *structure* identical so CBMC can't easily slice it away.
static inline uint16_t f_faulty(uint16_t x, uint16_t k, int r) {
  uint16_t a = x ^ k;
  uint16_t b = (uint16_t)(a + rotl16(a, 3));
  uint16_t c = (uint16_t)(b ^ rotl16(b, 6));
  uint16_t d = (uint16_t)(c + rotl16(c, (unsigned)(a & 15u)));
  // Inject stuck-at-1 into an internal signal at the chosen round only
  if (r == FAULT_ROUND) {
    d = (uint16_t)(d | (uint16_t)(1u << FAULT_BIT));
  }
  uint16_t t = (uint16_t)(((d & 0x1111u) << 3) ^ ((d & 0x2222u) >> 1)
                        ^ ((d & 0x4444u) >> 2) ^ ((d & 0x8888u) >> 3));
  return (uint16_t)(d ^ t);
}

// Simple key schedule that keeps things symbolic but tiny: two 16-bit words expanded on-the-fly.
static inline uint16_t rk(uint16_t k0, uint16_t k1, int r) {
  // Avoid large arrays: tiny arithmetic recurrence
  uint16_t mix = (uint16_t)(rotl16(k0, (unsigned)(r & 7)) ^ rotl16(k1, (unsigned)((r>>3) & 7)));
  return (uint16_t)(mix + (uint16_t)(0x9E37u * (uint16_t)r));
}

static void feistel_golden(uint16_t *L, uint16_t *R, uint16_t k0, uint16_t k1) {
  uint16_t l = *L, r = *R;
  for (int i = 0; i < ROUNDS; ++i) {
    uint16_t ki = rk(k0, k1, i);
    uint16_t tmp = (uint16_t)(l ^ f(r, ki));
    l = r;
    r = tmp;
  }
  *L = l; *R = r;
}

static void feistel_faulty(uint16_t *L, uint16_t *R, uint16_t k0, uint16_t k1) {
  uint16_t l = *L, r = *R;
  for (int i = 0; i < ROUNDS; ++i) {
    uint16_t ki = rk(k0, k1, i);
    uint16_t ff = f_faulty(r, ki, i);
    uint16_t tmp = (uint16_t)(l ^ ff);
    l = r;
    r = tmp;
  }
  *L = l; *R = r;
}

int main(void) {
  // Fully symbolic small inputs
  uint16_t L0 = nondet_uint16_t();
  uint16_t R0 = nondet_uint16_t();
  uint16_t K0 = nondet_uint16_t();
  uint16_t K1 = nondet_uint16_t();

  uint16_t lg = L0, rg = R0;
  uint16_t lf = L0, rf = R0;

  feistel_golden(&lg, &rg, K0, K1);
  feistel_faulty(&lf, &rf, K0, K1);

  // Force CBMC to find a counterexample (equivalence is false).
  assert(lg == lf && rg == rf);
  return 0;
}
