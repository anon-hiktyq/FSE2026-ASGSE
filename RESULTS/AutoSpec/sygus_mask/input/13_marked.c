/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
/* 2. FUNC CONTRACT */
void foo(int x, int y) {
  // loop body
  /* 1. LOOP INVARIANT */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
