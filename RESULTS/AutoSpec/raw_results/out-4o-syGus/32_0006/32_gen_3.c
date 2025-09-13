/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 0;
  loop invariant x <= n;
  loop invariant n - x + 1 == \at(n, Pre) - x + 1;
  loop invariant \forall integer k; 0 <= k <= \at(n, Pre) - x ==> x == n - k;
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
