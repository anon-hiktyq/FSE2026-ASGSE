void foo(int x, int y) {
  int i = x;
  int j = y;

  /*@
  loop invariant x >= 0;
  loop invariant x + y == i + j;
  loop assigns x;
  loop assigns y;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }

}
