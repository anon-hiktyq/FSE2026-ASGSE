
/*@
requires n > 0;
*/
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  
  /*@
  loop invariant k == i;
  loop invariant k <= n;
  loop invariant k <= i;
  loop invariant i == k;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant i + k <= 2*i;
  loop invariant \forall integer m; 0 <= m < i ==> m < n;
  loop invariant 0 <= n - i;
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
  loop invariant k == n - j;
  loop invariant j <= n;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant \forall integer m; 0 <= m < j ==> m < n;
  loop invariant \exists integer m; 0 <= m < n ==> k == n - m;
  loop invariant k + j == n;
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
