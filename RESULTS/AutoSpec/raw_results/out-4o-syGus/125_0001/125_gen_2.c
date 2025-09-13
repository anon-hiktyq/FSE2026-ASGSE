void foo(int x, int y) {
  int i = x;
  int j = y;
  
  /*@
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop invariant i - x == j - y;
  loop invariant (x == 0) ==> (i - j == y - 0);
  loop assigns x, y;
  */
  while (x != 0) {
    x = x - 1;
    y = y - 1;
  }
  // post-condition
  if(y != 0) {
    // @ assert i != j;
  }
}
