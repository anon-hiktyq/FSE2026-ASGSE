/*@
requires x == n;
requires x != 0;
*/
void foo(int x, int n) { 
  // loop body
  /*@
  loop invariant x == n - (n - x);
  loop invariant x <= n;
  loop invariant x + (n - x) == n;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }

}
