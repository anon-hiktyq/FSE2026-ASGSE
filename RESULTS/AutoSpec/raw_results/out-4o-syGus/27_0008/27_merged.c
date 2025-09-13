/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x <= n && x >= 1;
  loop invariant x <= n && n >= 0;
  loop invariant x + n == 2 * n;
  loop invariant x + (n - x) == n;
  loop invariant n >= 0 && x <= n;
  loop invariant n - x == \at(n,Pre) - \at(x,Pre);
  loop invariant \forall integer k; x <= k <= n ==> k > 0;
  loop invariant \forall integer k; n >= k >= x ==> k >= 1;
  loop invariant \forall integer k; n >= k >= x ==> k > 0;
  loop invariant \forall integer k; 1 <= k <= x ==> x - k >= 0;
  loop invariant \exists integer k; k == x && k <= n && k > 0;
  loop invariant 1 <= x;
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