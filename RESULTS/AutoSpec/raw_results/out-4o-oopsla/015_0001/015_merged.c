
/*@
requires n > 0;
requires k > n;
*/
void foo015(int n, int k) {

  int j = 0;

  /*@
  loop invariant n - j <= k;
  loop invariant n - j < k;
  loop invariant k == \at(k, Pre) - j;
  loop invariant j <= n;
  loop invariant j <= \at(n,Pre);
  loop invariant 0 <= j;
  loop assigns k;
  loop assigns j;
  */
  while( j < n ) {
    j++;
    k--;
  } 
  //@ assert k>=0;
}