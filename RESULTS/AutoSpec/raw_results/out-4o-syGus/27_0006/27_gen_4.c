/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant n - x >= 0;
  loop invariant x == n - (\at(x, Pre) - x);
  loop invariant \at(x, Pre) - x == n - x;
  loop invariant \at(n, Pre) == n;
  loop assigns x;
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