void foo(int x, int y) {
  int i = x;
  int j = y;
  
  /*@
  loop invariant y == j - (i - x);
  loop invariant i == x + (j - y);
  loop assigns y;
  loop assigns x;
  */
  while (x != 0) {
    x  = x - 1;
    y  = y - 1;
  }
// post-condition
  if(i == j) {
    //@assert(y == 0);
  }
}