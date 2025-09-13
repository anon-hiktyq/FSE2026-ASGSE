void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1 || n < 0;
  loop invariant x == n - (\at(x, Pre) - x);
  loop invariant x == n - (\at(n, Pre) - x);
  loop invariant x <= n;
  loop invariant n >= 0 ==> x <= n;
  loop invariant 1 <= x;
  loop invariant 1 <= x <= n || x < 1;
  loop invariant 1 <= x <= n || n < 0;
  loop invariant 0 <= x;
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
