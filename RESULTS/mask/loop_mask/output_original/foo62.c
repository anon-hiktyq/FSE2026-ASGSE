
/*@
    requires n >= 0;
*/
void foo62(int n) {
  int i, sum = 0;

  /*@
    loop invariant (i < \at(n,Pre)) ==> (sum == (i * (i - 1)) / 2);
    loop invariant (!(i < \at(n,Pre)) || (sum == (i * (i - 1)) / 2));
    loop invariant n == \at(n,Pre);
    loop assigns i, sum;
    loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    sum = sum + i;
  }

  /* mask_1 */
}
