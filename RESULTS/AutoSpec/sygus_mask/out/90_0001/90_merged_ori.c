void foo(int x) {
  int lock = 0;
  int y = x + 1;
  
  /*@
  loop invariant y == x + 1 || y > x;
  loop invariant y == x + 1 || y == x + 2;
  loop invariant y == x + 1 || (lock == 1 && x == y);
  loop invariant y == x + 1 || (lock == 0);
  loop invariant x == y || x < y;
  loop invariant x == y || x != y;
  loop invariant x == y || (x < y);
  loop invariant x <= y;
  loop invariant x <= x + 1;
  loop invariant x < y;
  loop invariant x != y;
  loop invariant lock == 0 || lock == 1;
  loop invariant lock == 0 ==> y > x;
  loop invariant lock == (x == y);
  loop invariant \forall integer k; k < y ==> k != x;
  loop assigns y;
  loop assigns x;
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
