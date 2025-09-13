/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // variable declarations
  int z1;
  int z2;
  int z3;

  // loop body
  /*@
  loop invariant y == \at(y, Pre) + 10 * (y - \at(y, Pre)) / 10;
  loop invariant y <= 10 + 10 * \at(y, Pre);
  loop invariant y <= 10 + 10 * \at(unknown(), Pre);
  loop invariant y <= 10 + 10 * \at(\loop_iteration, y);
  loop invariant y <= 10 + 10 * \at(\loop_iteration, \here);
  loop invariant y <= 10 + 10 * \at(\loop_iteration - 1, \pre);
  loop invariant y <= 10 + 10 * (\at(y, Here) / 10);
  loop invariant y % 10 == \at(y, \pre) % 10;
  loop invariant y % 10 == \at(y % 10, Pre);
  loop invariant x == \at(x, Pre) + 10 * (y - \at(y, Pre)) / 10;
  loop invariant x <= 10 + 10 * \at(y, Pre);
  loop invariant x <= 10 + 10 * \at(x, Pre);
  loop invariant x <= 10 + 10 * \at(unknown(), Pre);
  loop invariant x <= 10 + 10 * \at(\loop_iteration, x);
  loop invariant x <= 10 + 10 * \at(\loop_iteration, \here);
  loop invariant x <= 10 + 10 * \at(\loop_iteration - 1, \pre);
  loop invariant x <= 10 + 10 * (\at(x, Here) / 10);
  loop invariant x % 10 == \at(x, \pre) % 10;
  loop invariant x % 10 == \at(x % 10, Pre);
  loop invariant \forall integer k; k >= 0 ==> y == \at(y, Pre) + 10 * k;
  loop invariant \forall integer k; k >= 0 ==> x == \at(x, Pre) + 10 * k;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (y - \at(y, Here)) % 10 == 0;
  loop invariant (x - \at(x, Here)) % 10 == 0;
  loop assigns y;
  loop assigns x;
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
