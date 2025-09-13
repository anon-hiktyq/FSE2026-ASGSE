
/*@
requires n > 0;
*/
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  
  /*@
  loop invariant n - k == n - i;
  loop invariant n - k <= n;
  loop invariant n - k <= n || k + j <= n;
  loop invariant n - k <= n || j < n + 1;
  loop invariant n - k <= n || i <= k;
  loop invariant n - k <= n || i + k <= 2 * n;
  loop invariant n - k <= n || 0 <= j;
  loop invariant n - k <= n || 0 <= i + k;
  loop invariant n - k < n;
  loop invariant k == n - j;
  loop invariant k + j == n;
  loop invariant k + j <= n;
  loop invariant k + j <= n || j < n + 1;
  loop invariant k + j <= n || i <= k;
  loop invariant k + j <= n || i + k <= 2 * n;
  loop invariant k + j <= n || 0 <= j;
  loop invariant k + j <= n || 0 <= i + k;
  loop invariant k + j < n;
  loop invariant j <= n;
  loop invariant j <= n || n - k <= n;
  loop invariant j <= n || k + j <= n;
  loop invariant j <= n || j < n + 1;
  loop invariant j <= n || i <= k;
  loop invariant j <= n || i + k <= 2 * n;
  loop invariant j <= n || 0 <= n - k;
  loop invariant j <= n || 0 <= k + i;
  loop invariant j <= n || 0 <= j;
  loop invariant j <= n || 0 <= i + k;
  loop invariant j <= n + 1;
  loop invariant j < n;
  loop invariant j < n + 1;
  loop invariant j < n + 1 || i <= k;
  loop invariant j + k == n;
  loop invariant i <= k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i < k;
  loop invariant i + k == 2*k;
  loop invariant i + k == 2*i;
  loop invariant i + k == 2 * i;
  loop invariant i + k <= 2 * n;
  loop invariant i + k <= 2 * n || j < n + 1;
  loop invariant i + k <= 2 * n || i <= k;
  loop invariant i + k < 2 * n;
  loop invariant \forall integer m; 0 <= m < n - i ==> m + i < n;
  loop invariant \forall integer m; 0 <= m < k ==> m < n;
  loop invariant \forall integer m; 0 <= m < j ==> m < n;
  loop invariant \forall integer m; 0 <= m < i ==> k - m < n;
  loop invariant \forall integer m; 0 <= m < i ==> (i + m) < (2 * n);
  loop invariant 0 <= n - k;
  loop invariant 0 <= n - k || n - k <= n;
  loop invariant 0 <= n - k || k + j <= n;
  loop invariant 0 <= n - k || j < n + 1;
  loop invariant 0 <= n - k || i <= k;
  loop invariant 0 <= n - k || i + k <= 2 * n;
  loop invariant 0 <= n - k || 0 <= j;
  loop invariant 0 <= n - k || 0 <= i + k;
  loop invariant 0 <= k + i;
  loop invariant 0 <= k + i || n - k <= n;
  loop invariant 0 <= k + i || k + j <= n;
  loop invariant 0 <= k + i || j < n + 1;
  loop invariant 0 <= k + i || i <= k;
  loop invariant 0 <= k + i || i + k <= 2 * n;
  loop invariant 0 <= k + i || 0 <= n - k;
  loop invariant 0 <= k + i || 0 <= j;
  loop invariant 0 <= k + i || 0 <= i + k;
  loop invariant 0 <= j;
  loop invariant 0 <= j || j < n + 1;
  loop invariant 0 <= j || i <= k;
  loop invariant 0 <= j || i + k <= 2 * n;
  loop invariant 0 <= j || 0 <= i + k;
  loop invariant 0 <= i + k;
  loop invariant 0 <= i + k || j < n + 1;
  loop invariant 0 <= i + k || i <= k;
  loop invariant 0 <= i + k || i + k <= 2 * n;
  loop invariant 0 < n - k;
  loop invariant 0 < k + i;
  loop invariant 0 < j;
  loop invariant 0 < i + k;
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
