
/*@
    requires n >= 0;
*/
void foo62(int n) {
  int i, sum = 0;

  /*@
      loop invariant 0 <= i <= n;
      loop invariant sum == (\sum(j, 0, i-1, j));
      loop invariant n == \at(n,Pre);
      loop assigns i, sum;
      loop variant n - i;
  */
  for (i = 0; i < n; ++i) {
    sum = sum + i;
  }

  /*@ assert sum >= 0; */
}
