/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x == n - (n - x);
  loop invariant x == (n - (\at(x, LoopEntry) - x));
  loop invariant x <= n && x >= 1;
  loop invariant x <= \at(x, LoopEntry);
  loop invariant x + (n - x) == n;
  loop invariant n >= 0 ==> x <= n;
  loop invariant n - x == \at(x, LoopEntry) - x;
  loop invariant n - x == \at(n, LoopEntry) - x;
  loop invariant n - (n - \at(n, LoopEntry)) <= x;
  loop invariant \forall integer k; x > k >= 1 ==> k <= n;
  loop invariant \forall integer k; x <= n ==> (x + k == n || x + k <= n);
  loop invariant \forall integer k; n >= k >= x ==> k - x == n - \at(x, LoopEntry);
  loop invariant \forall integer k; n >= 0 ==> x <= n - k;
  loop invariant \forall integer k; 1 <= k <= n ==> x <= n - k;
  loop invariant \exists integer k; 1 <= k <= n && x == n - k;
  loop invariant \exists integer k; 0 <= k <= n - x && x == n - k;
  loop invariant \at(x, LoopEntry) - x == n - x;
  loop invariant 1 <= x;
  loop invariant 0 <= x;
  loop invariant 0 <= n;
  loop invariant 0 <= n - x;
  loop invariant 0 <= \at(x, LoopEntry) - x;
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
