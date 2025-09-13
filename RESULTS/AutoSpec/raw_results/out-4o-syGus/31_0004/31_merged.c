void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1 || n <= 0;
  loop invariant x >= 0 || n < 0;
  loop invariant x == n - (n - x);
  loop invariant x == n - ((n > 0) ? (n - x) : 0);
  loop invariant n > 0 ==> x >= 1 && x <= n;
  loop invariant n > 0 ==> x > 0 && x <= n;
  loop invariant n > 0 ==> x == n - (n - x);
  loop invariant n > 0 ==> x <= n && x > 0;
  loop invariant n > 0 ==> x + 1 >= 2;
  loop invariant \exists integer k; 1 <= k;
  loop invariant 0 <= x;
  loop invariant 0 < x;
  loop invariant (x == 1) ==> (\forall integer k; x <= k <= n ==> k > 0);
  loop invariant (n > 0) ==> x <= n;
  loop invariant (\exists integer k; 0 <= k <= n && x == n - k);
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
