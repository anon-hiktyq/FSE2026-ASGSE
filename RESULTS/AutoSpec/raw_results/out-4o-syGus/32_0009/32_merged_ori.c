/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x == n - \at(x, LoopEntry) + 1;
  loop invariant x == n - (\at(x, Pre) - x);
  loop invariant x == n - (\at(x, Pre) - n);
  loop invariant x == n - (\at(x, Pre) - 1);
  loop invariant x == n - (\at(n, Pre) - x);
  loop invariant x + (n - x) == n;
  loop invariant n >= 1 ==> x > 0;
  loop invariant n >= 0 ==> x <= n;
  loop invariant \forall integer k; x <= k <= n ==> k > 0;
  loop invariant \forall integer k; x + k == n ==> k >= 0;
  loop invariant \forall integer k; 1 <= k <= n ==> x <= k;
  loop invariant \forall integer k; 1 <= k <= n - x ==> k <= n;
  loop invariant \forall integer k; 1 <= k <= (n - x) ==> x == n - k;
  loop invariant \forall integer k; 0 <= k <= (n - x) ==> x == n - k;
  loop invariant \exists integer k; k == n - x && k >= 0;
  loop invariant 1 <= x;
  loop invariant 0 <= x;
  loop invariant 0 <= n - x;
  loop invariant x <= n;
  loop invariant 0 <= n;
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
