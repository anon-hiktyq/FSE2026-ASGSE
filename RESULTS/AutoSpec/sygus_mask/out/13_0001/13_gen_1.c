/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 2 + 2*count; // where count is the number of iterations
  loop invariant 0 <= y <= 2 + 2*count; // where count is the number of iterations
  loop assigns x;
  loop assigns y;
  loop assigns count; // if count is defined elsewhere to track iterations
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
