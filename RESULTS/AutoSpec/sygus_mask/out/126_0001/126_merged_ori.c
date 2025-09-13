void foo(int x, int y) {
  int i = x;
  int j = y;

  /*@
  loop invariant y == j - (i - x);
  loop invariant y <= j;
  loop invariant x <= i;
  loop invariant x + y == j;
  loop invariant i == x + (j - y);
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }

}
