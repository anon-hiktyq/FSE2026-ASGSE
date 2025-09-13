void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1 || n < 0;
  loop invariant x <= n;
  loop invariant x == n - (\at(n, Pre) - x);
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
