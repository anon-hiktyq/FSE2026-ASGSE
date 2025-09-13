/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant x <= n;
  loop invariant n >= 0;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}