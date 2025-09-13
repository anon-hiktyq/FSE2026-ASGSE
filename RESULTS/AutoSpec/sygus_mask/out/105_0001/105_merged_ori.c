/*@
requires n >= 0;
*/
void foo(int n) {
  int x = 0;
  
  /*@
  loop invariant x == old(x) + (n - old(n));
  loop invariant x == old(x) + (i - j);
  loop invariant x == \old(x) + (n - \old(n));
  loop invariant x == \old(x) + (1 * (x - \old(x)));
  loop invariant x <= n;
  loop invariant x < n ==> x + 1 <= n;
  loop invariant 0 <= x;
  loop assigns x;
  */
  while (x < n) {
    x = x + 1;
  }

}
