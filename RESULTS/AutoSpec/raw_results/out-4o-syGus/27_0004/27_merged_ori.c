/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x == n - (\at(x, Pre) - x);;
  loop invariant x == n - (\at(n, Pre) - x);;
  loop invariant x == \at(x, Pre) - (n - \at(n, Pre));
  loop invariant x <= n;;
  loop invariant x <= \at(x, Pre);
  loop invariant n >= 0 && x >= 1;
  loop invariant n - x == \at(x, Pre) - x;
  loop invariant n - x == \at(n, Pre) - \at(x, Pre);
  loop invariant n - x <= \at(x, Pre) - 1;
  loop invariant n % 2 == 0 || x >= 1;
  loop invariant \forall integer k; x <= k <= n ==> k >= 1;
  loop invariant \forall integer k; x <= k <= n ==> k > 0;;
  loop invariant \forall integer k; \at(x, Pre) >= k >= x ==> n >= k;
  loop invariant \forall integer k; 1 <= k <= (n - x) ==> x + k <= n;
  loop invariant \exists integer k; 1 <= k <= n ==> x == n - k;
  loop invariant \at(x, Pre) - x == n - x;
  loop invariant 1; <= x;
  loop invariant 1 <= x;
  loop invariant 0; <= n;
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