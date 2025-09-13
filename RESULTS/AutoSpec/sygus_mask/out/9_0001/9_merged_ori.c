/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 2 + 2*count; // where count is the number of iterations;
  loop invariant y <= 2 + 2*count;
  loop invariant y <= 2 + 2 * number_of_iterations;
  loop invariant y <= 2 + 2 * k; // where k is the number of iterations;
  loop invariant y <= 2 + 2 * iterations;
  loop invariant y <= 2 + 2 * (number of loop iterations);
  loop invariant y <= 2 + 2 * (number of iterations);
  loop invariant x <= 2 + 2*count; // where count is the number of iterations;
  loop invariant x <= 2 + 2*count;
  loop invariant x <= 2 + 2 * number_of_iterations;
  loop invariant x <= 2 + 2 * k; // where k is the number of iterations;
  loop invariant x <= 2 + 2 * iterations;
  loop invariant x <= 2 + 2 * (number of loop iterations);
  loop invariant x <= 2 + 2 * (number of iterations);
  loop invariant x - y == 0; // preserve any relation as per requirements;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (y - 2) % 2 == 0;
  loop invariant (x - 2) % 2 == 0;
  loop assigns y;
  loop assigns x;
  loop assigns count;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
