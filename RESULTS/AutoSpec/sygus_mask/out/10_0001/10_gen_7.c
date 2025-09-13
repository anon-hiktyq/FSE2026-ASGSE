/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 2 + 2 * k; // where k is the number of iterations
  loop invariant 0 <= y <= 2 + 2 * k; // where k is the number of iterations
  loop invariant x == y; // assuming x and y are equal at the beginning
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
