/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant x >= 0 && x <= 2 + 2 * iterations;
  loop invariant y >= 0 && y <= 2 + 2 * iterations;
  loop invariant x - y == 0;
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
