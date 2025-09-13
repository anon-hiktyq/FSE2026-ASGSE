/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // variable declarations
  int z1;
  int z2;
  int z3;

  // loop body
  /*@
  loop invariant 0 <= x <= 10 + 10 * k; // where k is the number of iterations executed
  loop invariant 0 <= y <= 10 + 10 * k; // where k is the number of iterations executed
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }

}
