void foo(int x, int y) {
  int i = x;
  int j = y;

  /*@
  loop invariant y == j - (i - x);
  loop invariant y <= j;
  loop invariant y <= j - i + x;
  loop invariant y <= j - (i - x);
  loop invariant y - x == j - i;
  loop invariant x == i - (j - y);
  loop invariant x == 0 ==> y == j - i;
  loop invariant x <= i;
  loop invariant i - x == j - y;
  loop invariant 0 <= i - x;
  loop invariant (i - x) == (j - y);
  loop assigns y;
  loop assigns x;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }
  // post-condition
  if (y != 0) {
    //@ assert i != j;
  }
}
