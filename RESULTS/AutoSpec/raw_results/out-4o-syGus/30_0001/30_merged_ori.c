/*@
requires (x == 100);
*/
void foo(int x) { 
  // loop body
  /*@
  loop invariant x;
  loop invariant x == \at(x, Pre) - \loop_iterations;
  loop invariant x <= 100;
  loop invariant \forall integer k; x <= k <= 100 ==> k > 0;
  loop invariant \exists integer n; 0 <= n <= 100 && x == 100 - n;
  loop invariant \exists integer k; x == 100 - k && 0 <= k <= 100;
  loop invariant \exists integer k; 0 <= k <= 100 && x == 100 - k;
  loop invariant 0 <= x;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }
  // post-condition
  // @ assert x == 0;
}
