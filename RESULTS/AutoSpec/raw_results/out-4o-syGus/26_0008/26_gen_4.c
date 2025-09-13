/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x > 0;
  loop invariant x >= 1;
  loop invariant n >= x;
  loop invariant n - x == \at(n, LoopEntry) - \at(x, LoopEntry);
  loop invariant x == \at(x, LoopEntry) - (\at(x, LoopEntry) - x);
  loop invariant x <= n;
  loop invariant n == x + (n - x);
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }
  // post-condition
  if (x != 1) {
    // @ assert n < 0;
  }
}
