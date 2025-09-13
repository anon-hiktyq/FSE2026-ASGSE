/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1;  
  loop invariant n >= 1;  
  loop invariant x + (n - x) == n;  
  loop invariant \at(x, Pre) - x == n - x;  
  loop invariant x <= \at(x, Pre);
  loop invariant x > 1 ==> n > 1;
  loop invariant x == n - (\at(x, Pre) - x);
  loop invariant x <= n;
  loop invariant n - (n - x) <= x;
  loop assigns x;
  */
  while (x > 1) {
    x  = x - 1;
  }
  // post-condition
  if (x != 1) {
    // @ assert n < 0;
  }
}
