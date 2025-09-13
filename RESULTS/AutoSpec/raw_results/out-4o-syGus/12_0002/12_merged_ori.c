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
  loop invariant y <= 10 + 10 * \count;
  loop invariant y <= 10 + 10 * \at(y, Pre);
  loop invariant y <= 10 + 10 * \at(\count, Pre);
  loop invariant y <= 10 + 10 * (\at(y,LoopEntry) / 10);
  loop invariant x <= 10 + 10 * \count;
  loop invariant x <= 10 + 10 * \at(y, Pre);
  loop invariant x <= 10 + 10 * \at(x, Pre);
  loop invariant x <= 10 + 10 * \at(\count, Pre);
  loop invariant x <= 10 + 10 * (\at(x,LoopEntry) / 10);
  loop invariant \at(y, Pre) <= y;
  loop invariant \at(x, Pre) <= x;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
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
