/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /*@
  loop invariant x >= 1;  
  loop invariant n - x >= 0;  
  loop invariant n - x == \at(n - x, Pre);  
  loop invariant x == \at(x, Pre) - (n - x);  
  loop invariant \forall integer k; x <= k <= n ==> k > 0;  
  loop invariant \exists integer k; x <= k <= n && k % 1 == 0;
  loop invariant x == n - (n - x);
  loop invariant x <= n;
  loop invariant x + 1 <= n + 1;
  loop invariant n == x + (n - x);
  loop invariant n == \at(n, Pre);
  loop invariant n != 1;
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
