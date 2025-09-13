void foo(int x, int y) {
  int i = x;
  int j = y;
  
  /*@
  loop invariant x >= 0;
  loop invariant y == j - (i - x);
  loop invariant \forall integer k; 0 <= k <= i - x ==> y == j - k;
  loop assigns x;
  loop assigns y;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }
  

}
