/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 20;
  loop invariant y <= 10 + 10 * \at_loop_count;
  loop invariant y <= 10 + 10 * \at(y,Pre);
  loop invariant y <= 10 + 10 * \at(unknown(), Pre);
  loop invariant y <= 10 + 10 * \at(\loop_iteration, Here);
  loop invariant y <= 10 + 10 * (\at(y,LoopEntry) / 10);
  loop invariant y <= 10 + 10 * (\at(y, Pre) / 10 + 1);
  loop invariant y % 10 == \at(y,LoopEntry) % 10;
  loop invariant y % 10 == \at(y, Pre) % 10;
  loop invariant x == y || x == y + 10;
  loop invariant x <= y;
  loop invariant x <= 20;
  loop invariant x <= 10 + 10 * \at_loop_count;
  loop invariant x <= 10 + 10 * \at(x,Pre);
  loop invariant x <= 10 + 10 * \at(unknown(), Pre);
  loop invariant x <= 10 + 10 * \at(\loop_iteration, Here);
  loop invariant x <= 10 + 10 * (\at(x,LoopEntry) / 10);
  loop invariant x <= 10 + 10 * (\at(x, Pre) / 10 + 1);
  loop invariant x % 10 == y % 10;
  loop invariant x % 10 == \at(x,LoopEntry) % 10;
  loop invariant x % 10 == \at(x, Pre) % 10;
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
  if (x == 20) {
    // @ assert y != 0;
  }
}
