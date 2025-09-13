/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x == n;
  loop invariant x == n || x == 1;
  loop invariant x == n - (n - x);
  loop invariant x == n - (iteration count);
  loop invariant x == n - (initial x - (n - x));
  loop invariant x <= n;
  loop invariant \forall integer k; 0 <= k < n - x ==> (x + k == n);
  loop invariant 1; < x;
  loop invariant 1 <= x;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }

}
