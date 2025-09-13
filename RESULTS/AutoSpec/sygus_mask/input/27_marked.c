/*@
requires x == n;
requires n >= 0;
*/
/* 2. FUNC CONTRACT */
void foo(int x, int n) {
  // loop body
  /* 1. LOOP INVARIANT */
  while (x > 1) {
    x  = x - 1;
  }

}