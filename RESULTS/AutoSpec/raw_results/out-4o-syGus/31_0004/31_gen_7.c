void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1 || n <= 0;
  loop invariant x <= n;
  loop invariant x == n - ((n > 0) ? (n - x) : 0);
  loop invariant n > 0 ==> x <= n && x > 0;
  loop invariant n <= 0 ==> x == n;
  loop assigns x;
  loop invariant x <= n;
  loop invariant n > 0 ==> x >= 1;
  loop invariant n > 0 ==> x > 0;
  loop invariant n <= 0 ==> x == n;
  loop invariant n <= 0 ==> x <= n;
  loop invariant (n > 0) ==> x >= 1;
  loop invariant (n <= 0) ==> x == n;
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
