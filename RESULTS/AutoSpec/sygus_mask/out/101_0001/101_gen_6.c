void foo(int n) {
  int x = 0;
  
  /*@
  loop invariant 0 <= x <= n;
  loop invariant x >= 0;
  loop invariant x == \old(x) + 1;
  loop assigns x;
  */
  while (x < n) {
    x = x + 1;
  }

}
