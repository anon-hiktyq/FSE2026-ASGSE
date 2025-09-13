/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant n - x >= 0;
  loop invariant x == n - (\at(x, LoopEntry) - x);
  loop invariant x <= n;
  loop invariant \forall integer k; 1 <= k <= n ==> x <= n - k;
  loop invariant \exists integer k; 1 <= k <= n && x == n - k;
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
