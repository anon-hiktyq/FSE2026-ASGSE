/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) { 
  // loop body
  /*@
  loop invariant x <= n;;
  loop invariant x <= n;
  loop invariant x + n == \text{initial}(x);
  loop invariant x + \result == n;
  loop invariant x + (n - x) == n;
  loop invariant x + (n - \old(x)) == n;
  loop invariant 0 <= x;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }

}
