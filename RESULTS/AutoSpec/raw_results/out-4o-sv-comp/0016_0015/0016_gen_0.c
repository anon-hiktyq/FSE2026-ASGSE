
/*@
requires n > 0;
*/
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  
  /*@
  loop invariant i <= n;
  loop invariant k == i;
  loop invariant 0 <= k <= n;
  loop invariant i == k;
  loop invariant i <= n;
  loop invariant \forall integer m; 0 <= m < i ==> m < n;
  loop invariant 0 <= k;
  loop invariant 0 <= i;
  
  loop invariant j <= n;
  loop invariant k + j == n;
  loop invariant k >= 0;
  loop invariant k == n - j;
  loop invariant j < n + 1;
  loop invariant \forall integer m; 0 <= m < j ==> m < n;
  loop invariant \forall integer m; 0 <= m < k ==> m < n;
  loop invariant k + j <= n;
  loop invariant k == i;
  loop invariant k <= n;
  loop invariant k < n + 1;
  loop invariant i == k;
  loop invariant i <= n;
  loop invariant i < n + 1;
  loop invariant \forall integer m; 0 <= m < i ==> m < n;
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
  loop invariant n - j == k;
  loop invariant k == n - j;
  loop invariant k <= n;
  loop invariant k <= n - j;
  loop invariant k + j == n;
  loop invariant k + j <= n;
  loop invariant j <= n;
  loop invariant j <= k + j;
  loop invariant j < n + 1;
  loop invariant j + k == n;
  loop invariant \forall integer m; 0 <= m < k ==> m < n;
  loop invariant \forall integer m; 0 <= m < j ==> m < n;
  loop invariant \forall integer m; 0 <= m < j ==> k + m < n;
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
