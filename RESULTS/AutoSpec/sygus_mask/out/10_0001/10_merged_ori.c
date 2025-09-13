/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= 2 + 2 * n; // where n is the number of iterations;
  loop invariant y <= 2 + 2 * k;;
  loop invariant y <= 2 + 2 * k; // where k is the number of iterations;
  loop invariant y <= 2 + 2 * k; // k is the number of iterations;
  loop invariant y <= 2 + 2 * iterations;
  loop invariant y <= 2 + 2 * iteration_count;
  loop invariant y <= 2 + 2 * \#(unknown());;
  loop invariant x == y; // assuming x and y are equal at the beginning;
  loop invariant x <= 2 + 2 * n; // where n is the number of iterations;
  loop invariant x <= 2 + 2 * k;;
  loop invariant x <= 2 + 2 * k; // where k is the number of iterations;
  loop invariant x <= 2 + 2 * k; // k is the number of iterations;
  loop invariant x <= 2 + 2 * iterations;
  loop invariant x <= 2 + 2 * iteration_count;
  loop invariant x <= 2 + 2 * \#(unknown());;
  loop invariant x - y == initial_x - initial_y; // where initial_x and initial_y are the values of x and y at the start of the loop;
  loop invariant x - y == 0;;
  loop invariant \forall integer k; 0 <= k < iteration_count ==> (x == 2 * (k + 1) + 0) && (y == 2 * (k + 1) + 0);
  loop invariant 0; <= k;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;;
  loop assigns y;
  loop assigns x;;
  loop assigns x;
  loop assigns k;;
  loop assigns iteration_count;
  */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
