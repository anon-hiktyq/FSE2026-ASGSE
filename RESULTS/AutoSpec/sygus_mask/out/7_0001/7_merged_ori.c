/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 10 + 10 * n; // where n is the number of iterations;
  loop invariant y <= 10 + 10 * k;;
  loop invariant y <= 10 + 10 * k; // where k is the number of iterations;
  loop invariant y <= 10 + 10 * iterations;
  loop invariant y <= 10 + 10 * count; // Here, 'count is the number of iterations executed;
  loop invariant y <= 10 + 10 * count;
  loop invariant x <= 10 + 10 * n; // where n is the number of iterations;
  loop invariant x <= 10 + 10 * k;;
  loop invariant x <= 10 + 10 * k; // where k is the number of iterations;
  loop invariant x <= 10 + 10 * iterations;
  loop invariant x <= 10 + 10 * count; // Here, 'count is the number of iterations executed;
  loop invariant x <= 10 + 10 * count;
  loop invariant \forall integer k; count <= k < count + 1 ==> (y == 10 + 10 * k);
  loop invariant \forall integer k; count <= k < count + 1 ==> (x == 10 + 10 * k);
  loop invariant 0; <= k;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  loop assigns k;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }
}
