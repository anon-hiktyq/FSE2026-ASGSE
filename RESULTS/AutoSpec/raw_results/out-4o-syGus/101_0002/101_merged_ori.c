void foo(int n) {
  int x = 0;
  
  /*@
  loop invariant x == n ==> n >= 0;
  loop invariant x == \old(x) + (x - \old(x));
  loop invariant x <= n;
  loop invariant n >= 0 ==> x == \at(x, Pre) + \at(x, Here);
  loop invariant n >= 0 ==> x <= n;
  loop invariant n < 0 ==> x == \at(x, Pre);
  loop invariant n < 0 ==> x == 0;
  loop invariant \forall integer k; 0 <= k < x ==> k < n;
  loop invariant 0 <= n - x;
  loop invariant 0 <= x;
  loop assigns x;
  */
  while (x < n) {
    x = x + 1;
  }
  // post-condition
  if (x != n) {
    // @ assert n < 0;
  }
}
