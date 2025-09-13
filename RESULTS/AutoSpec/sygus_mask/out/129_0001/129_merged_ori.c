void foo(int y) {
  int x = 1;
  
  /*@
  loop invariant x == 2^k where k is the number of iterations;
  loop invariant x == 2^k for some integer k >= 0;
  loop invariant x < y;
  loop invariant 1 <= x;
  loop assigns x;
  */
  while (x < y) {
    x = x + x;
  }

}
