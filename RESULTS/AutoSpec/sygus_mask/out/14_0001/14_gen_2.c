/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 2 + 2 * (iter + 1);
  loop invariant 0 <= y <= 2 + 2 * (iter + 1);
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
