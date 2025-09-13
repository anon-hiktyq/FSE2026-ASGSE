void foo(int n) {
  int x = 0;
  
  /*@
  loop invariant x <= n;
  loop invariant x >= 0;
  loop invariant x == \min(n, x) || x == \max(0, x);
  loop invariant \forall integer y; 0 <= y < x ==> y < n;
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
