/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x == n - (n - x);
  loop invariant x == \at(n, Pre) - (n - x);
  loop invariant x <= \at(n, Pre);
  loop invariant x + (n - x) == n;
  loop invariant x + (\at(n, Pre) - x) == n;
  loop invariant x + (\at(n, Pre) - n) == \at(n, Pre);
  loop invariant n >= 0 && x >= 1 && x <= n;
  loop invariant n - x == (\at(n, Pre) - x);
  loop invariant n - x + 1 == \at(n, Pre) - x + 1;
  loop invariant \forall integer k; x <= k <= n ==> k >= 1;
  loop invariant \forall integer k; x <= k <= n ==> k > 0;
  loop invariant \forall integer k; 0 <= k <= \at(n, Pre) - x ==> x == n - k;
  loop invariant \exists integer k; x == k && 1 <= k <= n;
  loop invariant \exists integer k; 0 <= k <= n && x == n - k;
  loop invariant \at(n, Pre) == n;
  loop invariant 1 <= x;
  loop invariant 0 <= x;
  loop invariant 0 <= n - x;
  loop invariant 0 < x;
  loop invariant x == n - (\at(n, Pre) - x);
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
