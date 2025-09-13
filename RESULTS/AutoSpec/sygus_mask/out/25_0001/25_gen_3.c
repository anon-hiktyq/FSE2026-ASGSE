/*@
requires (x == 10000);
*/
void foo(int x) {
  // loop body
  /*@
  loop invariant x >= 0;
  loop invariant x <= 10000;
  loop assigns x;
  */
  while ((x > 0)) {
    (x  = (x - 1));
  }

}
