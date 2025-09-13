void foo(int x, int y) {
  int i = x;
  int j = y;

  /*@
  loop invariant x >= 0;
  loop invariant \forall integer k; 0 <= k < i - x ==> x + k >= 0;
  loop invariant y == j - (i - x);
  loop invariant x <= i;
  loop invariant y <= j;
  loop assigns x, y;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }
  // post-condition
  if (y != 0) {
    // @ assert i != j;
  }
}
