void foo(int x) {
  int lock = 0;
  int y = x + 1;
  
  /*@
  loop invariant lock == 0 || lock == 1;
  loop invariant x == y || x != y;
  loop invariant y > x;
  loop invariant y == x + 1 || y == x + 2;
  loop assigns x;
  loop assigns y;
  loop assigns lock;
  */
  while (x != y) {
    if (unknown()) {
      lock = 1;
      x  = y;
    } else {
      lock = 0;
      x  = y;
      y  = y + 1;
    }
  }

}
