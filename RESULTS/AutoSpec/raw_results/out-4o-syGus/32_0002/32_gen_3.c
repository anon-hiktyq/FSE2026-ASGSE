/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant n >= 0;
  loop invariant x >= 1;
  loop invariant x == n - (\at(x, LoopEntry) - x);
  loop invariant x <= n && x >= 1;
  loop invariant x == n - (n - x);
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
