
/*@
requires n >= 0;
*/
void foo023(int n) {
  int i, sum = 0;
 
  /*@
  loop invariant 0 <= i <= n;
  loop invariant sum == \sum(0..i-1, \lambda integer k; k);
  loop invariant sum >= 0;
  loop assigns i;
  loop assigns sum;
  */
  for (i = 0; i < n; ++i){
    sum = sum + i;
  }

  // @ assert sum >= 0;
}