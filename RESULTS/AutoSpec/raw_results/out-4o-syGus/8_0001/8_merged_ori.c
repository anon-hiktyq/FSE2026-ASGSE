/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 10 + 10 * \at(y, Pre);
  loop invariant y <= 10 + 10 * \at(unknown(), Pre);
  loop invariant y <= 10 + 10 * \at(\loop_iteration_count, AfterLoop);
  loop invariant y <= 10 + 10 * \at(\loop_counter, Pre);
  loop invariant y <= 10 + 10 * \at(\count, Pre);
  loop invariant y <= 10 + 10 * (\at(y,Pre) / 10);
  loop invariant x <= 10 + 10 * \at(x, Pre);
  loop invariant x <= 10 + 10 * \at(unknown(), Pre);
  loop invariant x <= 10 + 10 * \at(\loop_iteration_count, AfterLoop);
  loop invariant x <= 10 + 10 * \at(\loop_counter, Pre);
  loop invariant x <= 10 + 10 * \at(\count, Pre);
  loop invariant x <= 10 + 10 * (\at(x,Pre) / 10);
  loop invariant x % 10 == y % 10;
  loop invariant \at(y, Pre) + 10 * \at(\loop_counter, Pre) == y;
  loop invariant \at(x, Pre) + 10 * \at(\loop_counter, Pre) == x;
  loop invariant \at(unknown(), Pre) ==> (x % 10 == 0 && y % 10 == 0);
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (y == 0 ==> x != 20);
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
