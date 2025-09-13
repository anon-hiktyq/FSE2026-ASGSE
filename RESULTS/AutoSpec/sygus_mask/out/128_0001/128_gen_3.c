void foo(int y) {
  int x = 1;
  
  /*@
  loop invariant 1 <= x < y;
  loop invariant x == 2^n where n is the number of iterations;
  loop assigns x;
  */
  while (x < y) {
    x = x + x;
  }

}
