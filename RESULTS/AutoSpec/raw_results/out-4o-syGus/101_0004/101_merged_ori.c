void foo(int n) {
  int x = 0;
  
  /*@
  loop invariant x >= 0 ==> n >= 0;
  loop invariant x == \min(n, x);
  loop invariant x == \min(n, x) || x == \max(0, x);
  loop invariant x == \min(n, \old(x) + n);
  loop invariant x <= n;
  loop invariant x <= n && 0 <= x;
  loop invariant x + (n - x) == n;
  loop invariant n >= 0 ==> x == n;
  loop invariant n >= 0 ==> x <= n;
  loop invariant n > 0 == > x <= n;
  loop invariant n < 0 ==> x == 0;
  loop invariant \forall integer y; 0 <= y < x ==> y < n;
  loop invariant \forall integer k; 0 <= k < x ==> k < n;
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
