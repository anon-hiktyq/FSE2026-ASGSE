/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant n - x == \at(n, LoopEntry) - x;
  loop invariant x >= n - (n - \at(n, LoopEntry));
  loop invariant \forall integer k; x <= n ==> (x + k == n || x + k <= n);
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
