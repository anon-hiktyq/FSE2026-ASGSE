/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x > 1 ==> n > 1 && n >= \at(x, Pre) - x;
  loop invariant x > 1 ==> n > 1 && n - x < n;
  loop invariant x == \at(x, Pre) - (\at(x, Pre) - x);
  loop invariant x == \at(x, Pre) - (\at(n, Pre) - n);
  loop invariant x == \at(n, Pre) - (\at(n, Pre) - x);
  loop invariant x <= \at(x, Pre);
  loop invariant x + (n - x) == n;
  loop invariant x + (\at(n, Pre) - n) == \at(x, Pre);
  loop invariant n > x ==> x > 1;
  loop invariant n - x == \at(x, Pre) - x;
  loop invariant n - x == \at(n, Pre) - \at(x, Pre);
  loop invariant n - x <= \at(n, Pre) - \at(x, Pre);
  loop invariant n - x <= (\at(x, Pre) - x);
  loop invariant \forall integer k; x <= k <= n ==> k >= 1;
  loop invariant \forall integer k; \at(x, Pre) >= k >= x ==> n >= k;
  loop invariant \exists integer k; 1 <= k <= x && n == k + (\at(x, Pre) - k);
  loop invariant \at(x, Pre) - x == n - x;
  loop invariant \at(x, Pre) - x == n - \at(n, Pre);
  loop invariant \at(x, Pre) - x == (\at(n, Pre) - n);
  loop invariant 1 <= x;
  loop invariant 1 <= n - (n - x);
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
