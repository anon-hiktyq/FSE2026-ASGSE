
/*@
requires n > 0;
requires k > n;
*/
void foo015(int n, int k) {

  int j = 0;

  /*@
  loop invariant 0 <= j <= n;
  loop invariant k == \at(k, Pre) - j;
  loop invariant k > n - j;
  loop assigns j;
  loop assigns k;
  */
  while( j < n ) {
    j++;
    k--;
  } 
  // @ assert k>=0;
}