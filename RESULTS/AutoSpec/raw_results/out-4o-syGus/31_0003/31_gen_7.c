void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant 1 <= x <= n;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }
  // post-condition
  if (x != 1) {
    // @ assert n < 0;
  }
}
