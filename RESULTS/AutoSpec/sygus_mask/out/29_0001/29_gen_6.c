/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) { 
  // loop body
  /*@
  loop invariant 0 <= x <= n;
  loop invariant x + (n - \old(x)) == n;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }

}
