/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1 && x <= n;
  loop invariant x == 1 || x >= 1 && n > 0;
  loop invariant x <= \at(x, Pre);
  loop invariant x + (n - \at(x, Pre)) == n;
  loop invariant x + (\at(x, Pre) - n) == 1;
  loop invariant n - x == \at(x, Pre) - x;
  loop invariant n - x == \at(x, Pre) - 1;
  loop invariant n - x == (\at(x, Pre) - x);
  loop invariant \forall integer k; x <= k <= n ==> k >= 1;
  loop invariant \forall integer k; k >= 0 ==> x == n - k;
  loop invariant \exists integer k; 0 <= k <= n && x == n - k;
  loop invariant \at(x, Pre) - x == n - x;
  loop invariant 1 <= x;
  loop invariant 0 <= n - x;
  loop invariant 0 <= \at(x, Pre) - x;
  loop invariant 0 <= (\at(x, Pre) - x);
  loop invariant x == n - (\at(x,Pre) - x);
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