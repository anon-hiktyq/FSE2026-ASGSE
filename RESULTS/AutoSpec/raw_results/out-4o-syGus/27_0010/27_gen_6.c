/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant n - x >= 0;
  loop invariant x >= 1;
  loop invariant x >= 1 && x <= n;
  loop invariant n == \at(x, Pre) + (n - x);
  loop invariant \forall integer k; x <= k <= n ==> k >= 1;
  loop invariant x == n - (\at(x, Pre) - x);
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