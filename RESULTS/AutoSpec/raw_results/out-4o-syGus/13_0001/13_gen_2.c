/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 2 + 2 * \at(unknown(), Pre);
  loop invariant 0 <= y <= 2 + 2 * \at(unknown(), Pre);
  loop invariant x == y;
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }
  // post-condition
  if (x == 4) {
    // @ assert y != 0;
  }
}
