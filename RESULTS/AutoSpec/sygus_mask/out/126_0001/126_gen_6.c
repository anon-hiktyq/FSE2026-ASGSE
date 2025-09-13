void foo(int x, int y) {
  int i = x;
  int j = y;

  /*@
  loop invariant 0 <= x <= i;
  loop invariant 0 <= y <= j;
  loop invariant y == j - (i - x);
  loop assigns x;
  loop assigns y;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }

}
