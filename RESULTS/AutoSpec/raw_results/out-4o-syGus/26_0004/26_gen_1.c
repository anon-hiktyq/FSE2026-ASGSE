/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1;  
  loop invariant n >= 1 ==> x <= n;
  loop invariant x == n - (\at(x, Pre) - \at(n, Pre));  
  loop invariant \exists integer k; 1 <= k <= n && x == k;
  loop invariant x <= n;
  loop invariant \forall integer k; n >= 1 ==> x <= n;
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
