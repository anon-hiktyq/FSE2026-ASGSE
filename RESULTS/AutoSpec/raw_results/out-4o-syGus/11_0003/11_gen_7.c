/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 10 + 10 * (\at(unknown(), Pre));
  loop invariant 0 <= y <= 10 + 10 * (\at(unknown(), Pre));
  loop invariant x % 10 == \at(x % 10, Pre);
  loop invariant y % 10 == \at(y % 10, Pre);
  loop assigns x, y;
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
