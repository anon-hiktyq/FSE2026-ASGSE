/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
/* 2. FUNC CONTRACT */
void foo(int x, int y) {
  // loop body
  /* 1. LOOP INVARIANT */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }

}
