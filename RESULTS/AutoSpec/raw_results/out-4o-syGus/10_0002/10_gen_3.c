/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 2 + 2 * \at(unknown(), Here);
  loop invariant 0 <= y <= 2 + 2 * \at(unknown(), Here);
  loop invariant (x - y) == \at(x - y, Pre);
  loop assigns x, y;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }
  // post-condition
  if (y == 0) {
    // @ assert x != 4;
  }
}
