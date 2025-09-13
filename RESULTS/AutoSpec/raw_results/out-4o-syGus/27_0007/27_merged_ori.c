/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x == n - \at(x, Pre) + 1;
  loop invariant x == n - \at(x - 1, Pre) + 1;
  loop invariant x <= n;
  loop invariant 1 <= x;
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