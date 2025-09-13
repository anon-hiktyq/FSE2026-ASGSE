/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant 1 <= x <= n;
  loop invariant x == n - (\at(n, Pre) - x);
  loop invariant \forall integer k; 1 <= k <= n - x ==> k <= n;
  loop invariant n >= 1 ==> x > 0;
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
