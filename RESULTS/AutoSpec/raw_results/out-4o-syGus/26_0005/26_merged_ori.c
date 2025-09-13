/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x == n - (n - x);
  loop invariant x <= n;
  loop invariant x + 1 <= n + 1;
  loop invariant x != 1;
  loop invariant x != 1 ==> x > 1;
  loop invariant n == x + (n - x);
  loop invariant n == \old(n);
  loop invariant n == \at(n, Pre);
  loop invariant n != 1;
  loop invariant 1 <= x;
  loop invariant 0 < x;
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
