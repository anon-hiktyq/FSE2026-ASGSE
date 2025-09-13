int unknown();
/*@
requires n > 0;
*/
void foo037(int n) {
  int x = 0;
  int m = 0;
 
  /*@
  loop invariant x <= n;
  loop invariant 0 <= x;
  loop invariant 0 <= m < n || m == 0;
  loop invariant 0 < n;
  loop invariant (x == 0 || (x > 0 ==> 0 <= m && m < x));
  loop invariant (x == 0 ==> m == 0) && (x > 0 ==> 0 <= m && m < x);
  loop invariant (m >= 0 && m < x) || m == 0;
  loop invariant (m >= 0 && m < x) || (x == 0 && m == 0);
  loop invariant (0 <= m && m < x) || x == 0;
  loop invariant (0 <= m && m < x) || m == 0;
  loop assigns x;
  loop assigns m;
  */
  while (x < n) {
    if (unknown()) {
      m = x;
    }
    x = x + 1;
  }
  // @ assert (n > 0) ==> (0 <= m && m < n);
}