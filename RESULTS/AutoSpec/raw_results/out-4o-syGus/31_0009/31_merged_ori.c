void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1 || n < 1;
  loop invariant x >= 1 || n < 0;
  loop invariant x > 1 || n <= 1;
  loop invariant x > 1 ==> n >= x;
  loop invariant x > 1 ==> n > 0;
  loop invariant x > 0 ==> n > 0;
  loop invariant x == n - (n - x);;
  loop invariant x == \at(x, Pre) - (\at(n, Pre) - n);;
  loop invariant x == \at(n, Pre) - (n - x);
  loop invariant x == 1 ==> n > 0;
  loop invariant x <= n || x < 0;
  loop invariant x <= n && x >= 0;;
  loop invariant x <= n && x >= 0;
  loop invariant x <= \at(n, Pre);
  loop invariant x + (\at(n, Pre) - n) == \at(x, Pre);
  loop invariant x + (\at(n, Pre) - n) == \at(n, Pre);
  loop invariant x % 2 == n % 2;
  loop invariant n >= 0 ==> x >= 1;;
  loop invariant n >= 0 ==> x >= 1;
  loop invariant n >= 0 ==> x >= 0;
  loop invariant n >= 0 ==> x > 0;
  loop invariant n > 0 ==> x >= 1;
  loop invariant n > 0 ==> x > 0 && n >= 1;
  loop invariant n < 0 || x > 0;
  loop invariant n < 0 ==> x == n;
  loop invariant n - (\at(n, Pre) - x) <= x;
  loop invariant \forall integer k; x <= k <= n ==> k >= 1;
  loop invariant \forall integer k; x <= k <= n ==> k > 1;
  loop invariant \forall integer k; x <= k <= n ==> k > 0;;
  loop invariant \forall integer k; 1 <= k <= n ==> x == n - k || x <= n - k;
  loop invariant 1 <= x;
  loop invariant 0; <= x;
  loop invariant 0 <= x;
  loop invariant (n > 1) ==> (x >= 1);
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
