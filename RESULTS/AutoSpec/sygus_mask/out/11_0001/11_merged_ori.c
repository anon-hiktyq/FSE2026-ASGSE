/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 10 + 10*count;
  loop invariant y <= 10 + 10 * n; // where n is the number of iterations;
  loop invariant y <= 10 + 10 * k; // where k is the number of iterations;
  loop invariant y <= 10 + 10 * iterations;
  loop invariant y <= 10 + 10 * \#(unknown() executions);
  loop invariant x <= 10 + 10*count;
  loop invariant x <= 10 + 10 * n; // where n is the number of iterations;
  loop invariant x <= 10 + 10 * k; // where k is the number of iterations;
  loop invariant x <= 10 + 10 * iterations;;
  loop invariant x <= 10 + 10 * iterations;
  loop invariant x <= 10 + 10 * \#(unknown() executions);
  loop invariant x - y == initial_x - initial_y;
  loop invariant \exists integer k; count == k;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= \#(unknown() executions);
  loop assigns y;
  loop assigns x;
  loop assigns count;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }

}
