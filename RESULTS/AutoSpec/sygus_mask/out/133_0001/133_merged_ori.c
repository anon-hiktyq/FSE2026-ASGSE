/*@
requires n >= 0;
*/
void foo(int n) {
  int x = 0;

  /*@
  loop invariant x == old(x) + (x - old(x));
  loop invariant x == \old(x) + 1 * (\old(x) < n);
  loop invariant x <= n;
  loop invariant x < n ==> x == \old(x) + 1;
  loop invariant x < n ==> x + 1 <= n;
  loop invariant 0 <= x;
  loop assigns x;
  */
  while (x < n) {
    x  = x + 1;
  }

}
