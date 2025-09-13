void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1 || x < 1;
  loop invariant x >= 1 || n < 0;
  loop invariant x > 1 ==> x - 1 >= 0;
  loop invariant x > 1 ==> n >= 1;
  loop invariant x > 1 ==> n > 0;
  loop invariant x == n - (n - x);
  loop invariant x == \at(n, Pre) - (\at(n, Pre) - x);
  loop invariant x == 1 || x < 1;
  loop invariant x < n || x == n;
  loop invariant x + (\at(n, Pre) - n) == \at(n, Pre);
  loop invariant n >= 1 ==> x >= 1;
  loop invariant n >= 1 ==> x <= n && x >= 1;
  loop invariant n >= 0 ==> x >= 1;
  loop invariant n >= 0 ==> x <= n && x >= 1;
  loop invariant n < 0 ==> x < 1;
  loop invariant \forall integer k; (n > 0) ==> (1 <= x <= n - k);
  loop invariant \exists integer m; 0 <= m <= n && x == n - m;
  loop invariant \exists integer k; x == n - k && k >= 0;
  loop invariant \exists integer k; k >= 0 && x == n - k;
  loop invariant \exists integer k; 0 <= k <= n && x == n - k;
  loop invariant 0 <= x;
  loop invariant 0 <= n - x;
  loop invariant 0 < x;
  loop invariant (\forall integer k; 1 <= k <= n ==> x <= n);
  loop invariant x == n - (\at(n, Pre) - x);
  loop invariant x <= n;
  loop invariant n >= 0 ==> x <= n;
  loop invariant 1 <= x <= n || x < 1;
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
