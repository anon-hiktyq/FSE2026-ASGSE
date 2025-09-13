void foo(int x) {
  int lock = 0;
  int y = x + 1;
  
  /*@
  loop invariant x <= y;
  loop invariant (lock == 1) ==> x == y;
  loop invariant (lock == 0) ==> x < y;
  loop assigns x;
  loop assigns lock;
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
