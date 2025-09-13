/*@
requires (x == 10000);
*/
void foo(int x) {
  // loop body
  /*@
  loop invariant 0 <= x <= 10000;
  loop invariant x == \at(x, Pre) - \at(x, Pre) + 10000;
  loop assigns x;
  */
  while ((x > 0)) {
    (x  = (x - 1));
  }
  // post-condition
  // @ assert  (x == 0) ;
}
