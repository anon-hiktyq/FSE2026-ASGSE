/*@
requires n < 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /*@
  loop invariant x >= 0 ==> n >= 0;
  loop invariant x <= n;
  loop invariant n < 0;
  loop invariant 0 <= x;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }
  // post-condition
  if (x != 0) {
    // @ assert n < 0;
  }
}
