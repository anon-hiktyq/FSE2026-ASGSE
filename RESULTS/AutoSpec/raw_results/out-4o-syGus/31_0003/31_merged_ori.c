void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x == n - (\at(x,Pre) - x);
  loop invariant x == n - (\at(x, Pre) - x);
  loop invariant x == n - (\at(x, Here) - \at(x, LoopEntry));
  loop invariant x <= n;
  loop invariant n > 0 ==> x >= 1;
  loop invariant n > 0 ==> x > 0;
  loop invariant n <= 0 ==> x == n;
  loop invariant n <= 0 ==> x <= n;
  loop invariant 1 <= x;
  loop invariant (n > 0) ==> x >= 1;
  loop invariant (n <= 0) ==> x == n;
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
