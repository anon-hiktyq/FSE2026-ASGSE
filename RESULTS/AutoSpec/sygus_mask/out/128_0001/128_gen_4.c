void foo(int y) {
  int x = 1;
  
  /*@
  loop invariant 1 <= x < y;
  loop invariant x == 1 << \floor(log2(x));
  loop assigns x;
  */
  while (x < y) {
    x = x + x;
  }

}
