/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x == n - (initial_x - x);
  loop invariant x <= n;
  loop invariant \forall integer k; 0 <= k < n - x ==> k < n;
  loop invariant 1 <= x;
  loop invariant 0 <= n;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}