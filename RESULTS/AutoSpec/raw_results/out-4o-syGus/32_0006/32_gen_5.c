/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant n >= x;
  loop invariant \at(n, Pre) == n;
  loop invariant n - x >= 0;
  loop invariant x == n - (\at(n, Pre) - x);
  loop invariant x <= n; 
  loop invariant n >= 0;
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
