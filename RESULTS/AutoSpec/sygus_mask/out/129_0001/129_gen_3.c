void foo(int y) {
  int x = 1;
  
  /*@
  loop invariant 1 <= x < y;
  loop invariant x == 2^k for some integer k >= 0;
  loop assigns x;
  */
  while (x < y) {
    x = x + x;
  }

}
