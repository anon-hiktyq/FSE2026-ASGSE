/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1 || n < 1;
  loop invariant x == n - (\at(n,Pre) - x);
  loop invariant x == n - (\at(n, Pre) - \at(x, Pre));
  loop invariant x == 1 || x <= n;
  loop invariant x != 1 ==> n > 1;
  loop invariant n >= 1 ==> x >= 1;
  loop invariant n >= 1 ==> x <= n;
  loop invariant n > 0 ==> x <= n;
  loop invariant n <= 0 ==> x == n;
  loop invariant n - (n - x) <= x;
  loop invariant n != x;
  loop invariant n != x ==> x < n;
  loop invariant \forall integer k; x <= n && k >= x ==> k - x >= 0;
  loop invariant \forall integer k; x <= k <= n ==> k > 1;
  loop invariant \forall integer k; 1 <= k <= n ==> k >= x;
  loop invariant \forall integer k; 0 <= k < n ==> k != x;
  loop invariant \exists integer k; x <= k;
  loop invariant \exists integer k; n >= k >= 1 && x == n - k;
  loop invariant \exists integer k; k >= 1 && x == n - k;
  loop invariant \exists integer k; 1 <= k <= n && x == k;
  loop invariant \exists integer k; 1 <= k <= n && x + k == n + 1;
  loop invariant 1 <= x;
  loop invariant 0 < x;
  loop invariant x <= n;
  loop invariant \forall integer k; n >= 1 ==> x <= n;
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
