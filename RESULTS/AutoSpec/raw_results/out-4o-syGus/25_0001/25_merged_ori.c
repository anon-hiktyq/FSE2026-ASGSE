/*@
requires (x == 10000);
*/
void foo(int x) {
  // loop body
  /*@
  loop invariant x == \at(x, Pre) - \at(x, Pre) + 10000;
  loop invariant x == \at(x, Pre) - \at(x, Here);
  loop invariant x == 10000 - \at(x, Pre);
  loop invariant x <= 10000;
  loop invariant \exists integer k; 0 <= k <= 10000 && x == 10000 - k;
  loop invariant 0 <= x;
  loop assigns x;
  */
  while ((x > 0)) {
    (x  = (x - 1));
  }
  // post-condition
  // @ assert  (x == 0) ;
}
