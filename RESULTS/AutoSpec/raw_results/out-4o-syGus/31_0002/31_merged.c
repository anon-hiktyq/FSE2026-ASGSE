void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1 || n <= 0;
  loop invariant x > 0 ==> n > 0;
  loop invariant x == n - (n - x);
  loop invariant x == n - (\at(n, Pre) - x);
  loop invariant x <= n && n - x >= 0;
  loop invariant x <= \at(n, Pre);
  loop invariant n >= 0 ==> x >= 1;
  loop invariant n > 0 ==> x >= 1;
  loop invariant n > 0 ==> x > 1;
  loop invariant n == \at(n, Pre);
  loop invariant n - x == \at(n, Pre) - \at(x, Here);
  loop invariant n - x <= n;
  loop invariant n - (\at(n,Pre) - x) <= x;
  loop invariant \exists integer k; 0 <= k < n ==> n - x == k;
  loop invariant \at(n, Pre) - x == n - x;
  loop invariant 1 <= x;
  loop invariant 0 <= x;
  loop invariant 0 < x;
  loop invariant 0 < x || n < 1;
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
