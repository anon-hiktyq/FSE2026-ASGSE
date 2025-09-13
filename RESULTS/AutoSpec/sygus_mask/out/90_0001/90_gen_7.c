void foo(int x) {
  int lock = 0;
  int y = x + 1;
  
  /*@
  loop invariant x <= y;
  loop invariant lock == (x == y);
  loop invariant y == x + 1 || (lock == 0);
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
