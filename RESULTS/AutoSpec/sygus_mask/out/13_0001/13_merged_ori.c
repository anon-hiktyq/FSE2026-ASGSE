/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y >= 0 && y <= 2 + 2 * iterations;
  loop invariant y <= 2 + 2*count; // where count is the number of iterations;
  loop invariant y <= 2 + 2*count;
  loop invariant y <= 2 + 2 * k;;
  loop invariant y <= 2 + 2 * iterations; // where iterations is the number of loop iterations;
  loop invariant y <= 2 + 2 * count; // where count is the number of iterations;
  loop invariant y <= 2 + 2 * \#(unknown());
  loop invariant y <= 2 + 2 * (unknown() ? 1 : 0);
  loop invariant x >= 0 && y >= 0;
  loop invariant x >= 0 && x <= 2 + 2 * iterations;
  loop invariant x <= 2 + 2*count; // where count is the number of iterations;
  loop invariant x <= 2 + 2*count;
  loop invariant x <= 2 + 2 * k;;
  loop invariant x <= 2 + 2 * iterations; // where iterations is the number of loop iterations;
  loop invariant x <= 2 + 2 * count; // where count is the number of iterations;
  loop invariant x <= 2 + 2 * \#(unknown());
  loop invariant x <= 2 + 2 * (unknown() ? 1 : 0);
  loop invariant x - y == 0;
  loop invariant 0; <= k;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  loop assigns count; // if count is defined elsewhere to track iterations;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
