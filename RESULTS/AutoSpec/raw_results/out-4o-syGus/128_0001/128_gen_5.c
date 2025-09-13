void foo(int y) {
  int x = 1;
  
  /*@
  loop invariant x >= 1;
  loop invariant x > 0;
  loop invariant x <= y;
  loop invariant x == 1 << (\at(x, Pre) - 1);
  loop assigns x;
  */
  while (x < y) {
    x = x + x;
  }
  // post-condition
  // @ assert x >= 1;
}
