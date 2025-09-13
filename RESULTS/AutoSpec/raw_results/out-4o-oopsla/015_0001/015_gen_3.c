
/*@
requires n > 0;
requires k > n;
*/
void foo015(int n, int k) {

  int j = 0;

  /*@
  loop invariant 0 <= j <= n;
  loop invariant k == \old(k) - j;
  loop invariant k >= \old(k) - n;
  loop assigns j, k;
  */
  while( j < n ) {
    j++;
    k--;
  } 
  // @ assert k>=0;
}