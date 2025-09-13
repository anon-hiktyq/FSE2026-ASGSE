void foo(int y) {
  int x = 1;
  
  /*@
  loop invariant x == 2^n where n is the number of iterations;
  loop invariant x == 2^n for some integer n >= 0;
  loop invariant x == 2^k for some integer k; k >= 0;
  loop invariant x == 2^k for some integer k >= 0;
  loop invariant x == 1 << \floor(log2(x));
  loop invariant x < y;
  loop invariant 1 <= x;
  loop assigns x;
  */
  while (x < y) {
    x = x + x;
  }

}
