/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y % 2 == \at(y, Pre) % 2;
  loop invariant x - y == \at(x, Pre) - \at(y, Pre);
  loop invariant x % 2 == \at(x, Pre) % 2;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (x - \at(x, Pre)) == (y - \at(y, Pre));
  loop assigns y;
  loop assigns x;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }
  // post-condition
  if (y == 0) {
    //@ assert x != 4;
  }
}
