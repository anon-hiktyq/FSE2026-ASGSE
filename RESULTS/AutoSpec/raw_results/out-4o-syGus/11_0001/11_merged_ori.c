/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 10 + 10 * \at(loop_entry, y);
  loop invariant y <= 10 + 10 * \at(\loop_count, Pre);
  loop invariant y <= 10 + 10 * (\at(y, Pre) / 10);
  loop invariant y <= 10 + 10 * (\at(y, Pre) / 10 + 1);
  loop invariant y <= 10 + 10 * (\at(unknown(), Pre) - unknown());
  loop invariant y % 10 == \at(y, Pre) % 10;
  loop invariant y % 10 == \at(loop_entry, y) % 10;
  loop invariant y % 10 == 0;
  loop invariant x <= 10 + 10 * \at(loop_entry, x);
  loop invariant x <= 10 + 10 * \at(\loop_count, Pre);
  loop invariant x <= 10 + 10 * (\at(x, Pre) / 10);
  loop invariant x <= 10 + 10 * (\at(x, Pre) / 10 + 1);
  loop invariant x <= 10 + 10 * (\at(unknown(), Pre) - unknown());
  loop invariant x % 10 == \at(x, Pre) % 10;
  loop invariant x % 10 == \at(loop_entry, x) % 10;
  loop invariant x % 10 == 0;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (y - \at(y, Pre)) % 10 == 0;
  loop invariant (x - \at(x, Pre)) % 10 == 0;
  loop assigns y;
  loop assigns x;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }
  // post-condition
  if (x == 20) {
    // @ assert y != 0;
  }
}
