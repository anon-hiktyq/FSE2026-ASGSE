/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant 0 <= x <= n;
  loop invariant x == n - i;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }

}
