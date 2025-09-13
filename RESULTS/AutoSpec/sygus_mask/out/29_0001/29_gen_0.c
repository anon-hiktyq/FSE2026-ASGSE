/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) { 
  // loop body
  /*@
  loop invariant x >= 0;
  loop invariant x + \result == n;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }

}
