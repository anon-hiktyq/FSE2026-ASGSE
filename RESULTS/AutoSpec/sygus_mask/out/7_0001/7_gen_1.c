/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 10 + 10 * count;
  loop invariant 0 <= y <= 10 + 10 * count;
  loop invariant \forall integer k; count <= k < count + 1 ==> (x == 10 + 10 * k);
  loop invariant \forall integer k; count <= k < count + 1 ==> (y == 10 + 10 * k);
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }
}
