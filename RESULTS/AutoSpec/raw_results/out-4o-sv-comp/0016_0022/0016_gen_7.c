
/*@
requires n > 0;
*/
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  
  /*@
  loop invariant k == i;
  loop invariant k <= i;
  loop invariant i == k;
  loop invariant i <= n;
  loop invariant 0 <= k;
  loop invariant 0 <= i;
  loop assigns k;
  loop assigns i;
  */
  while( i < n ) {
	  i++;
	  k++;
  }

  int j = 0;
 
  /*@
  loop invariant 0 <= j <= n;
  loop invariant k == n - j;
  loop invariant 0 <= k <= n;
  loop assigns j;
  loop assigns k;
  */
  while( j < n ) {
    // @ assert k > 0;*/
    j++;
    k--;
  }
}
