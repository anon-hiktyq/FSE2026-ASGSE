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
  loop invariant y == \at(y, Pre) + 10 * (\at(x, Pre) - x);
  loop invariant y <= 10 + 10 * \at(y, Pre);
  loop invariant y <= 10 + 10 * \at(loop_iteration, Here);
  loop invariant y <= 10 + 10 * \at(loop_entry, y);
  loop invariant y <= 10 + 10 * \at(\num_iterations, Pre);
  loop invariant y <= 10 + 10 * (x / 10);
  loop invariant y <= 10 + 10 * (\at(y, Pre) / 10);
  loop invariant y <= 10 + 10 * (\at(y, Pre) - 0);
  loop invariant y <= 10 + 10 * (\at(loop_entry_count, Here));
  loop invariant y % 10 == \at(y, Pre) % 10;
  loop invariant x == \at(x, Pre) + 10 * (\at(y, Pre) - y);
  loop invariant x <= 10 + 10 * \at(y, Pre);
  loop invariant x <= 10 + 10 * \at(loop_iteration, Here);
  loop invariant x <= 10 + 10 * \at(loop_entry, x);
  loop invariant x <= 10 + 10 * \at(\num_iterations, Pre);
  loop invariant x <= 10 + 10 * (y / 10);
  loop invariant x <= 10 + 10 * (\at(x, Pre) / 10);
  loop invariant x <= 10 + 10 * (\at(x, Pre) - 0);
  loop invariant x <= 10 + 10 * (\at(loop_entry_count, Here));
  loop invariant x - y == \at(loop_entry, x) - \at(loop_entry, y);
  loop invariant x % 10 == \at(x, Pre) % 10;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (x - y) % 10 == 0;
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
