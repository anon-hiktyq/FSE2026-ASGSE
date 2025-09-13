/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 2 + 2*count;
  loop invariant y <= 2 + 2 * n; // where n is the number of iterations;
  loop invariant y <= 2 + 2 * n;
  loop invariant y <= 2 + 2 * iterations;
  loop invariant y <= 2 + 2 * (iteration count);
  loop invariant y <= 2 + 2 * (iter + 1);
  loop invariant y <= 2 + 2 * (i + 1);
  loop invariant x <= 2 + 2*count;
  loop invariant x <= 2 + 2 * n; // where n is the number of iterations;
  loop invariant x <= 2 + 2 * iterations;
  loop invariant x <= 2 + 2 * (iteration count);
  loop invariant x <= 2 + 2 * (iter + 1);
  loop invariant x <= 2 + 2 * (i + 1);
  loop invariant x - y == 0;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (x - y) == (initial_x - initial_y); // where initial_x and initial_y are the values of x and y at the start of the loop;
  loop assigns y;
  loop assigns x;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
