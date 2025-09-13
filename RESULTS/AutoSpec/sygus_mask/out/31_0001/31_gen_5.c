void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant 1 <= x <= n + 1;
  loop invariant x == n - i; // where i is the number of iterations
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}
