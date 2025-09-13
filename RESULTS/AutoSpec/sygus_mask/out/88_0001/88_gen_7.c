void foo(int x) {
  int lock = 0;
  int y = x + 1;
  
  /*@
  loop invariant lock == 0 || lock == 1;
  loop invariant x + 1 == y;
  loop invariant x == y || x < y;
  loop assigns lock;
  loop assigns x;
  loop assigns y;
  */
  while (x != y) {
    if (unknown()) {
      lock = 1;
      x = y;
    } else {
      lock = 0;
      x = y;
      y = y + 1;
    }
  }

}
