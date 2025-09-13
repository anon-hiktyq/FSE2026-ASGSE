
/*@
requires n >= 0;
*/
void foo023(int n) {
  int i, sum = 0;
 
  /*@
  loop invariant sum == \sum{0 <= k < i} k;
  loop invariant sum == (i*(i-1))/2;
  loop invariant sum == (i * (i - 1)) / 2;
  loop invariant i <= n;
  loop invariant 0 <= sum;
  loop invariant 0 <= i;
  loop assigns sum;
  loop assigns i;
  */
  for (i = 0; i < n; ++i){
    sum = sum + i;
  }

  // @ assert sum >= 0;
}