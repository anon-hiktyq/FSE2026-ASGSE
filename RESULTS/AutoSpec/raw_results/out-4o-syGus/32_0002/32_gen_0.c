/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 0;
  loop invariant \forall integer k; n >= 0 ==> x <= n - k;
  loop invariant x == (n - (\at(x, LoopEntry) - x));
  loop invariant x == n - (n - x);
  loop invariant n >= 0 ==> x <= n;
  loop invariant x == n - (\at(x, LoopEntry) - x);
  loop invariant x <= n;
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
