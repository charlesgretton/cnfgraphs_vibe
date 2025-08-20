// stuck_at_1_cbmc.c
// CBMC harness to expose a stuck-at-1 fault on internal net `n`
// in simple logic: y = !(a & b).

#include <assert.h>

// CBMC provides these nondet stubs; only declare them.
_Bool nondet_bool(void);

static _Bool golden_logic(_Bool a, _Bool b) {
  _Bool n = a && b;   // internal wire
  _Bool y = !n;       // output
  return y;
}

static _Bool faulty_logic(_Bool a, _Bool b) {
  (void)a; (void)b;
  _Bool n_faulty = 1; // <-- stuck-at-1 fault on internal wire `n`
  _Bool y_faulty = !n_faulty;
  return y_faulty;
}

int main(void) {
  _Bool a = nondet_bool();
  _Bool b = nondet_bool();

  _Bool y_golden = golden_logic(a, b);
  _Bool y_faulty = faulty_logic(a, b);

  // If the fault is detectable, there exists (a,b) such that outputs differ.
  // We assert equality so CBMC will produce a counterexample where they are NOT equal.
  assert(y_golden == y_faulty);

  return 0;
}
