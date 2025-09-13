void foo(int x, int y) {
  int i = x;
  int j = y;

  /*@
  loop invariant x + i == j + y;
  loop invariant x >= 0;
  loop assigns x;
  loop assigns y;
  loop assigns i;
  loop assigns j;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }

}
