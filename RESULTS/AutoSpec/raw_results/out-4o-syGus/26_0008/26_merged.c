/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x == \at(x, LoopEntry) - (\at(x, LoopEntry) - x);
  loop invariant x + (n - x) == n;
  loop invariant x != 1 ==> x >= 2;
  loop invariant x != 1 ==> x <= n && x > 1;
  loop invariant x != 0;
  loop invariant n - x == n - x;
  loop invariant n - x == \at(n, LoopEntry) - \at(x, LoopEntry);
  loop invariant \forall integer k; x <= k <= n ==> k >= 1;
  loop invariant \forall integer k; x <= k <= n ==> k > 0;
  loop invariant \exists integer k; x <= k <= n && k == x;
  loop invariant \exists integer k; x <= k <= n && k == n;
  loop invariant \exists integer k; k == x && k >= 1;
  loop invariant \exists integer k; 1 <= k <= n && x == n - k + 1;
  loop invariant \exists integer k; 0 <= k <= n && x + k == n;
  loop invariant 1 <= x;
  loop invariant 1 <= n;
  loop invariant 0 <= n - x;
  loop invariant 0 < x;
  loop invariant 0 < n;
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
