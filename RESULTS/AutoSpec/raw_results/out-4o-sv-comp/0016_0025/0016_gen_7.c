
/*@
requires n > 0;
*/
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  
  /*@
  loop invariant i + k == 2*i; 
  loop invariant \forall integer m; i <= m < n ==> k == i;
  loop invariant \exists integer m; 0 <= m < n ==> i == n - m;
  loop invariant n - i == k;
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
  loop invariant n - j == k;
  loop invariant k == n - j;
  loop invariant k <= n;
  loop invariant k <= n - j;
  loop invariant k + j == n;
  loop invariant k + j <= 2*n;
  loop invariant j <= n;
  loop invariant j <= n - k;
  loop invariant j + k == n;
  loop invariant \forall integer p; 0 <= p < j ==> p < n;
  loop invariant \forall integer m; j <= m < n ==> k >= 0;
  loop invariant \forall integer m; 0 <= m < j ==> n - m > 0;
  loop invariant \forall integer m; 0 <= m < j ==> m < n;
  loop invariant \forall integer m; 0 <= m < j ==> 0 <= k;
  loop invariant \exists integer m; 0 <= m < n ==> k == n - m;
  loop invariant 0 <= n - j;
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
