/*@
requires (x == 10000);
*/
void foo(int x) {
  // loop body
  /*@
  loop invariant x == 10000 - \#(0..(10000 - x));
  loop invariant x == (10000 - i);
  loop invariant x <= 10000;
  loop invariant \old(x) == (x + \#iterations);
  loop invariant 0 <= x;
  loop assigns x;;
  loop assigns x;
  loop assigns i;
  */
  while ((x > 0)) {
    (x  = (x - 1));
  }

}
