
/*@
requires n > 0;
*/
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  
  /*@
  loop invariant 0 <= i <= n;
  loop invariant 0 <= k <= n;
  loop invariant i == k;
  loop assigns i, k;
  */
  while( i < n ) {
	  i++;
	  k++;
  }

  int j = 0;
 
  while( j < n ) {
    // @ assert k > 0;*/
    j++;
    k--;
  }
}
