/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 2 + 2 * \at(x, Pre);
  loop invariant 0 <= y <= 2 + 2 * \at(y, Pre);
  loop invariant x % 2 == \at(x, Pre) % 2;
  loop invariant y % 2 == \at(y, Pre) % 2;
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
