/*@
requires (x == 10000);
*/
/* 2. FUNC CONTRACT */
void foo(int x) {
  // loop body
  /* 1. LOOP INVARIANT */
  while ((x > 0)) {
    (x  = (x - 1));
  }

}
