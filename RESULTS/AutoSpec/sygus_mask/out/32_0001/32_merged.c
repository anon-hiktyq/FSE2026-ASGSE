/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x <= n;
  loop invariant x <= n + 1;
  loop invariant 0 <= x;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}
