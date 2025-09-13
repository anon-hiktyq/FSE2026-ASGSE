/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 10;
  loop invariant y <= 10 + 10 * k; // where k is the number of iterations;
  loop invariant y <= 10 + 10 * k; // where k is the number of iterations completed;
  loop invariant y <= 10 + 10 * k; // k is the number of iterations;
  loop invariant y <= 10 + 10 * k;
  loop invariant y <= 10 + 10 * \#(unknown());
  loop invariant x <= 10;
  loop invariant x <= 10 + 10 * k; // where k is the number of iterations;
  loop invariant x <= 10 + 10 * k; // where k is the number of iterations completed;
  loop invariant x <= 10 + 10 * k; // k is the number of iterations;
  loop invariant x <= 10 + 10 * k;
  loop invariant x <= 10 + 10 * \#(unknown());
  loop invariant \forall integer k; 0 <= k <= \#(unknown()) ==> y == 10 + 10 * k;
  loop invariant \forall integer k; 0 <= k <= \#(unknown()) ==> x == 10 + 10 * k;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }

}
