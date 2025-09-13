void foo(int x, int y) {
  int i = x;
  int j = y;

  /*@
  loop invariant 0 <= x <= i;
  loop invariant y == j - (i - x);
  loop invariant x + y == j;
  loop assigns x;
  loop assigns y;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }

}
