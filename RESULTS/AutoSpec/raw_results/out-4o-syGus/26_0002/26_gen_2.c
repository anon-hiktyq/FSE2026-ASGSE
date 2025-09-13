/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant \at(x, Pre) - x == n - x;
  loop invariant \forall integer k; \at(x, Pre) >= k >= x ==> n >= k;
  loop invariant \exists integer k; 1 <= k <= x && n == k + (\at(x, Pre) - k);
  loop invariant n - x <= (\at(x, Pre) - x);
  loop invariant x > 1 ==> n > 1;
  loop invariant x == n - (\at(x, Pre) - x);
  loop invariant x <= n;
  loop invariant n - (n - x) <= x;
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
