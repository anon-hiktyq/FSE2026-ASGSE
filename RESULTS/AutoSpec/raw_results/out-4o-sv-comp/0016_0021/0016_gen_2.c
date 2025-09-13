
/*@
requires n > 0;
*/
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  
  /*@
  loop invariant 0 <= i <= n;
  loop invariant k == i;
  loop assigns i;
  loop assigns k;
  
  loop invariant 0 <= j <= n;
  loop invariant n - j == k;
  loop assigns j;
  loop assigns k;
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
