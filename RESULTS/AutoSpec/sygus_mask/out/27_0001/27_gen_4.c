/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant 1 <= x <= n;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}