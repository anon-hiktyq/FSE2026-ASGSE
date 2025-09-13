/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x <= n;
  loop invariant x != 1;
  loop invariant x != 1 ==> n < 0;
  loop invariant n == \old(x);
  loop invariant n == \old(n);
  loop invariant \forall integer k; n >= 1 ==> x <= n;
  loop invariant \exists integer k; 0 <= k <= n-1 && x == n - k;
  loop invariant 1 <= x;
  loop invariant 0 < x;
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
