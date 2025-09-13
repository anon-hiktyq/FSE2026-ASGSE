/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x <= n;
  loop invariant x != 1;
  loop invariant n == x + (n - x);
  loop invariant n == \old(n);
  loop invariant \forall integer k; x <= k <= n ==> k > 1;
  loop invariant 1 <= x;
  loop invariant 0 < n;
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
