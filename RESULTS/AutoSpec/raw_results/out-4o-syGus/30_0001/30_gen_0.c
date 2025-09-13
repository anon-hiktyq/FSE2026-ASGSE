/*@
requires (x == 100);
*/
void foo(int x) { 
  // loop body
  /*@
  loop invariant 0 <= x <= 100;
  loop invariant \exists integer n; 0 <= n <= 100 && x == 100 - n;
  loop assigns x;
  */
  while (x > 0) {
    x  = x - 1;
  }
  // post-condition
  // @ assert x == 0;
}
