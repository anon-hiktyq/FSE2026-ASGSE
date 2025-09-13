/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1;
  loop invariant x == n - (iteration count);
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}
