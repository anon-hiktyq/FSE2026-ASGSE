/*@
requires (x == 100);
*/
void foo(int x) { 
  // loop body
  /*@
  loop invariant x >= 0;
  loop invariant x <= 100;
  loop invariant \exists integer k; 0 <= k <= 100 && x == 100 - k;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }
  // post-condition
  // @ assert x == 0;
}
