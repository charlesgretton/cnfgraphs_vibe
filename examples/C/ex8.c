// cbmc_stuck_at1_heavy.c
// A CBMC-hard harness: deep ARX pipeline + large dataflow + stuck-at-1 fault.
//
// Goal: make CBMC build a very large, low-sliceability formula that still admits
// a counterexample, so solving can take minutes.
//
// Safe C: all shifts masked, no UB, fixed bounds (so --unwind is exact).

#include <stdint.h>
#include <assert.h>

// ---------- Tunables ----------
#ifndef ROUNDS
#define ROUNDS 512        // increase to make CBMC slower (e.g., 512 or 1024)
#endif

#ifndef MSG_LEN
#define MSG_LEN 2048      // increase to bloat the formula (e.g., 2048 or 4096)
#endif

#ifndef FAULT_ROUND
#define FAULT_ROUND (ROUNDS - 16)  // late injection so it propagates through many ops
#endif

#ifndef FAULT_WORD
#define FAULT_WORD 7       // which state word to corrupt
#endif

#ifndef FAULT_BIT
#define FAULT_BIT 15       // which bit is stuck-at-1
#endif
// -----------------------------

// CBMC nondeterministic generators
uint32_t nondet_uint(void);

// Rotate-left by (r & 31) to avoid UB; works for any r.
static inline uint32_t rotl32(uint32_t x, uint32_t r) {
    return (x << (r & 31)) | (x >> ((32 - r) & 31));
}

// Quarter-round (ChaCha-esque but customized to frustrate simplification).
static inline void qround(uint32_t s[16], int a, int b, int c, int d, uint32_t tweak) {
    // Data-dependent rotation counts (masked) make back-propagation nastier.
    uint32_t ra = (s[a] ^ tweak) & 31;
    uint32_t rb = (s[b] + tweak) & 31;
    uint32_t rc = (s[c] ^ (tweak << 1)) & 31;
    uint32_t rd = (s[d] + (tweak >> 1)) & 31;

    s[a] += s[b]; s[d] ^= s[a]; s[d] = rotl32(s[d], ra);
    s[c] += s[d]; s[b] ^= s[c]; s[b] = rotl32(s[b], rb);
    s[a] += s[b]; s[d] ^= s[a]; s[d] = rotl32(s[d], rc);
    s[c] += s[d]; s[b] ^= s[c]; s[b] = rotl32(s[b], rd);
}

// One round = 4 quarter-rounds with varying index patterns, keyed by i.
static inline void round_mix(uint32_t s[16], uint32_t key) {
    // Vary positions each round in a simple modular pattern to keep dependencies wide.
    int o = (int)(key & 3u) * 4;
    qround(s, (0+o)&15, (4+o)&15, (8+o)&15, (12+o)&15, key ^ 0x9e3779b9u);
    qround(s, (1+o)&15, (5+o)&15, (9+o)&15, (13+o)&15, key ^ 0x85ebca6bu);
    qround(s, (2+o)&15, (6+o)&15, (10+o)&15,(14+o)&15, key ^ 0xc2b2ae35u);
    qround(s, (3+o)&15, (7+o)&15, (11+o)&15,(15+o)&15, key ^ 0x27d4eb2fu);
}

// Stream-mix to force dependence on a big message array (thwarts slicing).
static inline void stream_mix(uint32_t s[16], uint32_t m, uint32_t i) {
    // Different injection points to spread influence.
    s[(i+0) & 15] ^= m + (i * 0x9e3779b9u);
    s[(i+5) & 15] += rotl32(m ^ (i * 0x85ebca6bu), (m + i) & 31);
    s[(i+9) & 15] ^= rotl32(m + (i * 0xc2b2ae35u), (m >> 3) & 31);
    s[(i+13)& 15] += m ^ rotl32(i, (m >> 7) & 31);
}

// Golden pipeline
static void golden(uint32_t state_out[16],
                   const uint32_t seed[16],
                   const uint32_t msg[MSG_LEN]) {
    uint32_t s[16];
    // Seed state (non-volatile to keep CBMC's SSA big but well-defined)
    for (int i = 0; i < 16; ++i) s[i] = seed[i];

    // Big streaming + rounds
    for (uint32_t i = 0; i < MSG_LEN; ++i) {
        stream_mix(s, msg[i], i);
        round_mix(s, s[(i*5u + 3u) & 15] ^ i);
    }

    // Final avalanche
    for (int r = 0; r < ROUNDS; ++r) {
        round_mix(s, (uint32_t)r ^ s[(r*7) & 15]);
    }

    for (int i = 0; i < 16; ++i) state_out[i] = s[i];
}

// Faulty pipeline with stuck-at-1 on an internal bit at FAULT_ROUND in the final avalanche.
static void faulty(uint32_t state_out[16],
                   const uint32_t seed[16],
                   const uint32_t msg[MSG_LEN]) {
    uint32_t s[16];
    for (int i = 0; i < 16; ++i) s[i] = seed[i];

    for (uint32_t i = 0; i < MSG_LEN; ++i) {
        stream_mix(s, msg[i], i);
        round_mix(s, s[(i*5u + 3u) & 15] ^ i);
    }

    for (int r = 0; r < ROUNDS; ++r) {
        if (r == FAULT_ROUND) {
            // Inject a stuck-at-1 on FAULT_BIT of s[FAULT_WORD]
            s[FAULT_WORD] = s[FAULT_WORD] | (1u << FAULT_BIT);
        }
        round_mix(s, (uint32_t)r ^ s[(r*7) & 15]);
    }

    for (int i = 0; i < 16; ++i) state_out[i] = s[i];
}

int main(void) {
    // Large, fully symbolic inputs that feed the whole network.
    uint32_t seed[16];
    uint32_t msg[MSG_LEN];

    for (int i = 0; i < 16; ++i) seed[i] = nondet_uint();
    for (int i = 0; i < MSG_LEN; ++i) msg[i]  = nondet_uint();

    uint32_t g[16], f[16];
    golden(g, seed, msg);
    faulty(f, seed, msg);

    // Prove equivalence -> CBMC must find a counterexample.
    for (int i = 0; i < 16; ++i) {
        assert(g[i] == f[i]);
    }
    return 0;
}
