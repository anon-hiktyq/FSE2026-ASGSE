/*@
requires (x == 100);
*/
void foo(int x) { 
  // loop body
  /*@
  loop invariant x >= 0;
  loop invariant \old(x) == 100;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }

}
