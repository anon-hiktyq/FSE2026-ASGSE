void foo(int n) {
  int x = 0;
  
  /*@
  loop invariant x < n ==> x < n;
  loop invariant x < n ==> x + 1 <= n;
  loop invariant x < n ==> \exists integer k; k == x;
  loop invariant 0 <= x;
  loop assigns x;
  */
  while (x < n) {
    x = x + 1;
  }

}
