/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant 0 <= x <= n;
  loop invariant x >= 1;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}
