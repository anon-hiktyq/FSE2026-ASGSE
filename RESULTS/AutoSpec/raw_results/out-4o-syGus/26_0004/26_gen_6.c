/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant x >= n - (n - x);
  loop invariant \forall integer k; x <= n && k >= x ==> k - x >= 0;
  loop invariant \exists integer k; x <= k <= n;
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
