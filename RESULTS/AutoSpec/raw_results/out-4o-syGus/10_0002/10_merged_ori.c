/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 2 + 2*\at(loop_counter, Here);
  loop invariant y <= 2 + 2 * \at(y, Pre);
  loop invariant y <= 2 + 2 * \at(y, Pre) / 2;
  loop invariant y <= 2 + 2 * \at(unknown(), Pre);
  loop invariant y <= 2 + 2 * \at(unknown(), Here);
  loop invariant y <= 2 + 2 * (\at(y, Pre) / 2);;
  loop invariant y % 2 == \at(y, Pre) % 2;
  loop invariant y % 2 == 0;
  loop invariant x <= y;
  loop invariant x <= 2 + 2*\at(loop_counter, Here);
  loop invariant x <= 2 + 2 * \at(y, Pre) / 2;
  loop invariant x <= 2 + 2 * \at(x, Pre);
  loop invariant x <= 2 + 2 * \at(unknown(), Pre);
  loop invariant x <= 2 + 2 * \at(unknown(), Here);
  loop invariant x <= 2 + 2 * (\at(x, Pre) / 2);;
  loop invariant x - y == \at(x, Pre) - \at(y, Pre);
  loop invariant x % 2 == y % 2;
  loop invariant x % 2 == \at(x, Pre) % 2;
  loop invariant x % 2 == 0;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (x - y) == \at(x - y, Pre);
  loop invariant (x - y) == (\at(x, Pre) - \at(y, Pre));
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
