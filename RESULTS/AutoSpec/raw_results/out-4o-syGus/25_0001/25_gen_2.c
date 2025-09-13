/*@
requires (x == 10000);
*/
void foo(int x) {
  // loop body
  /*@
  loop invariant x >= 0;
  loop invariant x <= 10000;
  loop invariant \exists integer k; 0 <= k <= 10000 && x == 10000 - k;
  loop assigns x;
  */
  while ((x > 0)) {
    (x  = (x - 1));
  }
  // post-condition
  // @ assert  (x == 0) ;
}
