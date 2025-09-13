/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 2 + 2 * iterations;
  loop invariant 0 <= y <= 2 + 2 * iterations;
  loop invariant x - y == initial_x - initial_y; // where initial_x and initial_y are the values of x and y at the start of the loop
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
