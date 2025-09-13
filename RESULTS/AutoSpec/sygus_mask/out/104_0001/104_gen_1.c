void foo(int n) {
  int x = 0;

  /*@
  loop invariant 0 <= x <= n;
  loop invariant x < n ==> \exists integer k; 0 <= k < x;
  loop assigns x;
  */
  while (x < n) {
    x = x + 1;
  }

}
