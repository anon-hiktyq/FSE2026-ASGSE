
/*@
requires n > 0;
*/
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  
  /*@
  loop invariant n - i == n - k;
  loop invariant k == i;
  loop invariant k <= n;
  loop invariant i == k;
  loop invariant i <= n;
  loop invariant i <= k;
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
  loop invariant n - k == j;
  loop invariant k == n - j;
  loop invariant j <= n;
  loop invariant 0 <= k <= n;
  loop invariant 0 <= j;
  loop invariant k == n - j;
  loop invariant k <= n;
  loop invariant j <= n;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop assigns k;
  loop assigns j;
  */
  while( j < n ) {
    // @ assert k > 0;*/
    j++;
    k--;
  }
}
