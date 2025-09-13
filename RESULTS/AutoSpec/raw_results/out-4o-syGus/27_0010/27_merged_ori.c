/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1 && x <= n;
  loop invariant x == x + (n - x);
  loop invariant x == n - (n - x);
  loop invariant x == n - (\at(x, Pre) - x) && x <= n;
  loop invariant x == \at(x, Pre) - (n - x);
  loop invariant x + (n - x) == n;
  loop invariant x + (n - \at(x, Pre)) == n;
  loop invariant x + (\at(x, Pre) - x) == n;
  loop invariant x + (\at(x, Pre) - n) == \at(x, Pre);
  loop invariant n == \at(x, Pre) + (n - x);
  loop invariant n - x == \at(x, Pre) - x;
  loop invariant n - x == \at(n, Pre) - \at(x, Pre);
  loop invariant n - x == (\at(x, Pre) - x);
  loop invariant \forall integer k; x <= k <= n ==> k >= 1;
  loop invariant \at(x, Pre) == n;
  loop invariant \at(x, Pre) - x == n - x;
  loop invariant \at(x, Pre) - n <= x;
  loop invariant 1 <= x;
  loop invariant 0 <= x;
  loop invariant 0 <= n - x;
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