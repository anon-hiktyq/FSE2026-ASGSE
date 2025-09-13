/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1 ==> x == n - (n - x);
  loop invariant x + (n - x) == n;
  loop invariant x % 2 == n % 2;
  loop invariant n <= x + 1;
  loop invariant \forall integer k; x <= k <= n ==> k > 0;
  loop invariant \forall integer k; n >= k >= x ==> k >= 1;
  loop invariant \forall integer k; 1 <= k <= (n - x) ==> x == n - k;
  loop invariant \forall integer k; 0 <= k <= n - x ==> x <= n - k;
  loop invariant \forall integer k; 0 <= k <= (n - x) ==> x + k == n;
  loop invariant \exists integer k; 1 <= k <= n && x == k;
  loop invariant \exists integer k; 0 <= k <= n && x == n - k;
  loop invariant 1 <= x;
  loop invariant 0 <= x;
  loop invariant 0 <= n - x;
  loop invariant 0 <= (n - x);
  loop invariant 0 < x;
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
