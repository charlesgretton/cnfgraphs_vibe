// cbmc_planted3sat.c
// CBMC harness that encodes a planted random 3-SAT instance.
// - N_VARS symbolic boolean inputs
// - N_CLAUSES fixed clauses (each clause has 3 literals)
// The generator uses a fixed pseudo-random seed so the instance is deterministic.
// Adjust N_VARS and N_CLAUSES to tune hardness (higher may be harder).

#include <assert.h>
#include <stdint.h>

// Tunables
#ifndef N_VARS
#define N_VARS 200
#endif

#ifndef N_CLAUSES
#define N_CLAUSES 850
#endif

// --- CBMC nondet boolean ---
_Bool nondet_bool(void);

// --- Small portable xorshift32 PRNG for deterministic instance generation ---
static uint32_t rng_state = 0xC0FFEEu;
static uint32_t xorshift32(void) {
    uint32_t x = rng_state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    return (rng_state = x ? x : 0xdeadbeefu);
}

// Generate a planted solution (sol[i] gives the value of var i in solution).
// Then produce clauses so that every clause is satisfied by the planted solution
// (i.e., for each clause we ensure at least one literal matches the planted bit).
// Clauses are stored as signed ints: >0 means variable index+1 positive literal,
// <0 means negated literal.
static void generate_instance(int clauses[N_CLAUSES][3], _Bool sol[N_VARS]) {
    // initialize PRNG to a deterministic seed (you can change this number)
    rng_state = 0xC0FFEEu;

    // plant a random solution
    for (int i = 0; i < N_VARS; ++i) {
        sol[i] = (xorshift32() & 1u) ? 1 : 0;
    }

    // build clauses
    for (int c = 0; c < N_CLAUSES; ++c) {
        // pick three *distinct* variable indices
        int a = xorshift32() % N_VARS;
        int b = xorshift32() % N_VARS;
        int d = xorshift32() % N_VARS;
        // ensure distinctness (simple loop)
        while (b == a) b = xorshift32() % N_VARS;
        while (d == a || d == b) d = xorshift32() % N_VARS;

        // For each literal we randomly decide polarity, but we ensure clause
        // has at least one literal that's true under planted sol.
        // Choose a "guaranteed-satisfier" among the three positions.
        int pos = (int)(xorshift32() % 3u);

        int lits[3];
        int idxs[3] = {a, b, d};

        for (int i = 0; i < 3; ++i) {
            if (i == pos) {
                // make literal match planted solution
                if (sol[idxs[i]]) lits[i] = (idxs[i] + 1);   // positive literal
                else lits[i] = -(idxs[i] + 1);               // negated literal
            } else {
                // random polarity (can accidentally match also)
                lits[i] = ((xorshift32() & 1u) ? (idxs[i] + 1) : -(idxs[i] + 1));
            }
        }
        clauses[c][0] = lits[0];
        clauses[c][1] = lits[1];
        clauses[c][2] = lits[2];
    }
}

// Evaluate the clause (three literals) given boolean variable array vars[].
static _Bool eval_clause(const _Bool vars[N_VARS], int lit0, int lit1, int lit2) {
    _Bool a = (lit0 > 0) ? vars[lit0 - 1] : !vars[(-lit0) - 1];
    _Bool b = (lit1 > 0) ? vars[lit1 - 1] : !vars[(-lit1) - 1];
    _Bool c = (lit2 > 0) ? vars[lit2 - 1] : !vars[(-lit2) - 1];
    return a || b || c;
}

int main(void) {
    // symbolic variables
    _Bool vars[N_VARS];
    for (int i = 0; i < N_VARS; ++i) vars[i] = nondet_bool();

    // instance storage (deterministically generated)
    static int clauses[N_CLAUSES][3];
    static _Bool planted_sol[N_VARS];

    generate_instance(clauses, planted_sol);

    // Optionally: you can assert that the planted_sol actually satisfies all clauses.
    // (This is just a sanity check and will not constrain the symbolic search.)
    for (int c = 0; c < N_CLAUSES; ++c) {
        // sanity: planted solution must satisfy clause
        _Bool sat_by_planted = eval_clause(planted_sol, clauses[c][0], clauses[c][1], clauses[c][2]);
        // this should always be true
        assert(sat_by_planted);
    }

    // Now require CBMC to find a valuation of 'vars' satisfying every clause.
    for (int c = 0; c < N_CLAUSES; ++c) {
        _Bool ok = eval_clause(vars, clauses[c][0], clauses[c][1], clauses[c][2]);
        // Force CBMC to find a model where every clause is true:
        assert(ok);
    }

    return 0;
}
