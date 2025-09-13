/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 2 + 2 * iteration_count;
  loop invariant 0 <= y <= 2 + 2 * iteration_count;
  loop invariant \forall integer k; 0 <= k < iteration_count ==> (x == 2 * (k + 1) + 0) && (y == 2 * (k + 1) + 0);
  loop assigns x;
  loop assigns y;
  loop assigns iteration_count;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
