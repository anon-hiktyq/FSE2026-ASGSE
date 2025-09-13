/*@
requires (x == 10000);
*/
void foo(int x) {
  // loop body
  /*@
  loop invariant 0 <= x <= 10000;
  loop invariant x == 10000 - \#(0..(10000 - x));
  loop assigns x;
  */
  while ((x > 0)) {
    (x  = (x - 1));
  }

}
