/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant x + 1 >= n;
  loop invariant 0 <= x <= n;
  loop invariant \exists integer k; 0 <= k <= n && x == n - k;
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
