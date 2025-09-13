#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Taken from "Counterexample Driven Refinement for Abstract Interpretation" (TACAS'06) by Gulavani
 */
/*@
requires n > 0;
*/
void foo(int n) {
  int x = 0;
  int m = 0;
  /*@
  loop invariant x == n ==> (0 <= m && m < n);
  loop invariant x == 0 || (0 <= m && m < x);
  loop invariant x <= n;
  loop invariant m < n;
  loop invariant \exists integer k; 0 <= k < x ==> m == k || m == 0;
  loop invariant 0 <= x;
  loop invariant 0 <= m;
  loop invariant 0 <= m < n || x == 0;
  loop invariant 0 <= m < n || m == 0;
  loop invariant (x == 0 || m >= 0) && m < n;
  loop assigns x;
  loop assigns m;
  */
  while (x < n) {
    if (unknown1()) {
      m = x;
    }
    x = x + 1;
  }
  if (n > 0) {
    // @ assert 0 <= m && m < n;
  }
}