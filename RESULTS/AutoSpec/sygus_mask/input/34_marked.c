/*@
requires n >= 0;
*/
/* 2. FUNC CONTRACT */
void foo(int n) {
  int x = n;
  // loop body
  /* 1. LOOP INVARIANT */
  while (x > 0) {
    x  = x - 1;
  }

}
