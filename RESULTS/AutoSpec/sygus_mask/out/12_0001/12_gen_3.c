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
  loop invariant x >= 0 && x <= 10;
  loop invariant y >= 0 && y <= 10;
  loop invariant \forall integer k; 0 <= k < x && k <= 10 ==> (x + 10*k) <= 10;
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }

}
