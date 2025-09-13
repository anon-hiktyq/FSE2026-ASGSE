void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant n - x <= n;
  loop invariant x >= 1;
  loop invariant x > 0 ==> n > 0;
  loop invariant x <= n;
  loop invariant \exists integer k; 0 <= k < n ==> n - x == k;
  loop invariant x == n - (\at(n,Pre) - x);
  loop invariant x <= n;
  loop invariant n > 0 ==> x > 0;
  loop invariant n <= 0 ==> x == n;
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
