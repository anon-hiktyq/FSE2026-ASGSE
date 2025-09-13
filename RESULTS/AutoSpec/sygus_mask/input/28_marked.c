/*@
requires x == n;
requires x != 0;
*/
/* 2. FUNC CONTRACT */
void foo(int x, int n) { 
  // loop body
  /* 1. LOOP INVARIANT */
  while (x > 0) {
    x  = x - 1;
  }

}
