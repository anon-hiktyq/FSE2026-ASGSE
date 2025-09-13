int unknown();
/*@
requires n > 0;
*/
void foo037(int n) {
  int x = 0;
  int m = 0;
 
  /*@
  loop invariant 0 <= x <= n;
  loop invariant (0 <= m && m < x) || m == 0;
  loop assigns x, m;
  */
  while (x < n) {
    if (unknown()) {
      m = x;
    }
    x = x + 1;
  }
  // @ assert (n > 0) ==> (0 <= m && m < n);
}