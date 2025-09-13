/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 10 + 10 * (\at(x,LoopEntry) / 10);
  loop invariant 0 <= y <= 10 + 10 * (\at(y,LoopEntry) / 10);
  loop invariant x % 10 == \at(x,LoopEntry) % 10;
  loop invariant y % 10 == \at(y,LoopEntry) % 10;
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
