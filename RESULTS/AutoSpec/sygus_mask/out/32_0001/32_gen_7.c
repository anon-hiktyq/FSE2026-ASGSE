/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant 1 <= x <= n + 1;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}
