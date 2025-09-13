void foo(int x, int y) {
  int i = x;
  int j = y;

  /*@
  loop invariant y == j - x;
  loop invariant y == i - x;
  loop invariant x <= i;
  loop invariant x + y == i + j;
  loop invariant x + i == j + y;
  loop invariant i - x == j - y;
  loop invariant \forall integer k; i >= k >= x ==> y == j - k;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  loop assigns j;
  loop assigns i;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }

}
