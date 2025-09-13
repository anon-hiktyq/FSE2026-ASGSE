/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x > 1 ==> x == \at(x, Pre) - (\at(x, Pre) - x);
  loop invariant x > 1 ==> n > x;;
  loop invariant x > 1 ==> n > 1;;
  loop invariant x > 1 ==> n > 1;
  loop invariant x > 0 ==> n > 0;
  loop invariant x == n - (n - x);;
  loop invariant x == \at(x, Pre) - (n - x);;
  loop invariant x == \at(x, Pre) - (n - x);
  loop invariant x == \at(n, Pre) - (n - x);
  loop invariant x <= n && x >= 1;
  loop invariant x <= \at(x, Pre);
  loop invariant x + (n - x) == n;
  loop invariant n - x == \at(n, Pre) - x;;
  loop invariant n - x == \at(n, Pre) - x;
  loop invariant n - x == \at(n - x, Pre);;
  loop invariant \forall integer k; x <= k <= n ==> k >= 1;
  loop invariant \forall integer k; x <= k <= n ==> k > 0;;
  loop invariant \forall integer k; 1 <= k <= n ==> x + k - 1 <= n;
  loop invariant \exists integer k; x <= k <= n && k % 1 == 0;;
  loop invariant \at(x, Pre) - x == n - x;
  loop invariant \at(n, Pre) == n;
  loop invariant 1; <= x;
  loop invariant 1; < n;
  loop invariant 1 <= x;
  loop invariant 1 < n;
  loop invariant 0; <= n - x;
  loop invariant 0 <= n - x;
  loop invariant 0 < x;
  loop invariant x == n - (n - x);
  loop invariant x <= n;
  loop invariant x + 1 <= n + 1;
  loop invariant n == x + (n - x);
  loop invariant n == \at(n, Pre);
  loop invariant n != 1;
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
