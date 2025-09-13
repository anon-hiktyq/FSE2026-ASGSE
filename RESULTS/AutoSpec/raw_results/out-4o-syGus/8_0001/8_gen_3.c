/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 10 + 10 * \at(\loop_counter, Pre);
  loop invariant 0 <= y <= 10 + 10 * \at(\loop_counter, Pre);
  loop invariant \at(x, Pre) + 10 * \at(\loop_counter, Pre) == x;
  loop invariant \at(y, Pre) + 10 * \at(\loop_counter, Pre) == y;
  loop assigns x, y;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }
  // post-condition
  if (y == 0) {
    // @ assert x != 20;
  }
}
