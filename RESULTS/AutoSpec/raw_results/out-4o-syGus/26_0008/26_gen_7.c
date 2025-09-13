/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x > 0;
  loop invariant n > 0;
  loop invariant n - x >= 0;
  loop invariant \exists integer k; 1 <= k <= n && x == n - k + 1;
  loop invariant x <= n;
  loop invariant n == x + (n - x);
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
