/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x == n - (\at(x, LoopEntry) - x);
  loop invariant 1 <= x <= n;
  loop invariant \at(x, LoopEntry) - x >= 0;
  loop invariant n - x >= 0;
  loop invariant \at(x, LoopEntry) - x == n - x;
  loop invariant x == n - (\at(x, LoopEntry) - x);
  loop invariant x <= n;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }
  // post-condition
  if (n >= 0) {
    // @ assert x == 1;
  }
}
