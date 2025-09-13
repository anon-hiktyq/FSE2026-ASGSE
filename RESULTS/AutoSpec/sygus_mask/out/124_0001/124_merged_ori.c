void foo(int x, int y) {
  int i = x;
  int j = y;
  
  /*@
  loop invariant y == j - (i - x);
  loop invariant i == x + (j - y);
  loop invariant \forall integer k; 0 <= k <= i - x ==> y == j - k;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }
  

}
