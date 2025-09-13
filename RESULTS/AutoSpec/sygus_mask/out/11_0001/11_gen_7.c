/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant 0 <= x <= 10 + 10 * \#(unknown() executions);
  loop invariant 0 <= y <= 10 + 10 * \#(unknown() executions);
  loop invariant \#(unknown() executions) >= 0;
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }

}
