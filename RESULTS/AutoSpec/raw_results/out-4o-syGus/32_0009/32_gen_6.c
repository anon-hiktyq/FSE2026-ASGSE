/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant 1 <= x <= n;
  loop invariant x == n - \at(x, LoopEntry) + 1;
  loop invariant 0 <= x;
  loop invariant n >= 0;
  loop invariant \forall integer k; 1 <= k <= n ==> x <= k;
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
