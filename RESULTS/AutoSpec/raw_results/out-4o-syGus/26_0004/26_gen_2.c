/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x > 0;
  loop invariant n >= 1 ==> x >= 1;
  loop invariant x >= 1 || n < 1;
  loop invariant x == n - (\at(n, Pre) - \at(x, Pre));
  loop invariant x != 1 ==> n > 1;
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
