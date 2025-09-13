void foo(int x, int y) {
  int i = x;
  int j = y;

  /*@
  loop invariant y == j - x;
  loop invariant 0 <= x <= i;
  loop invariant \forall integer k; i >= k >= x ==> y == j - k;
  loop assigns x;
  loop assigns y;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }

}
