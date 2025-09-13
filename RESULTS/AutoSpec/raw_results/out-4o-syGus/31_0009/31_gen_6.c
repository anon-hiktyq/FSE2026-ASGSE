void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 0;
  loop invariant x >= n - (\at(n, Pre) - x);
  loop invariant n >= 0 ==> x > 0;
  loop invariant x > 1 ==> n > 0;
  loop invariant \forall integer k; 1 <= k <= n ==> x == n - k || x <= n - k;
  loop invariant x == 1 ==> n > 0;
  loop invariant x > 1 ==> n >= 1;
  loop invariant x == n - (\at(n, Pre) - x);
  loop invariant x <= n;
  loop invariant x <= n || n < 0;
  loop invariant n > 0 ==> x > 0;
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
