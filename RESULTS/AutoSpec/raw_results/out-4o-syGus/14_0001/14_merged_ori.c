/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= x;
  loop invariant y <= 4;
  loop invariant y <= 2 + 2*\at(unknown(), Pre);
  loop invariant y <= 2 + 2 * \at(y,Pre);
  loop invariant y <= 2 + 2 * \at(y, Pre);
  loop invariant y <= 2 + 2 * \at(unknown(), Pre);
  loop invariant y <= 2 + 2 * (x - 0);
  loop invariant x == y;
  loop invariant x <= 4;
  loop invariant x <= 2 + 2*\at(unknown(), Pre);
  loop invariant x <= 2 + 2 * \at(x,Pre);
  loop invariant x <= 2 + 2 * \at(x, Pre);
  loop invariant x <= 2 + 2 * \at(unknown(), Pre);
  loop invariant x <= 2 + 2 * (y - 0);
  loop invariant x - y == 0;
  loop invariant \at(x, Pre) - x == \at(y, Pre) - y;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
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
