void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant x <= n;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}
