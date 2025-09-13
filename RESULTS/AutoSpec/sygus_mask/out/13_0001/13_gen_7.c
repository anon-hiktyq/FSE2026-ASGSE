/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant x >= 0 && y >= 0;
  loop invariant x <= 2 + 2 * (unknown() ? 1 : 0);
  loop invariant y <= 2 + 2 * (unknown() ? 1 : 0);
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
