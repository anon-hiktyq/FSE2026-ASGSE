/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant 0 <= x <= n;
  loop invariant n >= 0;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }
  // post-condition
  if (n >= 0) {
    // @ assert x == 0;
  }
}
