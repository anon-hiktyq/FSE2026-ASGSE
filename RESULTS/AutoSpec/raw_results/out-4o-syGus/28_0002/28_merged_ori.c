/*@
requires x == n;
requires x != 0;
*/
void foo(int x, int n) { 
  // loop body
  /*@
  loop invariant x == n - \at(x, Pre);
  loop invariant x <= n;
  loop invariant n > 0 ==> x >= 0;
  loop invariant n == \old(x);
  loop invariant \exists integer k; 0 <= k <= n && x == n - k;
  loop invariant 0 <= x;
  loop invariant 0 <= n;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }
  // post-condition
  if (x != 0) {
    // @ assert n < 0;
  }
}
