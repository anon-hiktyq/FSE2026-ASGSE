
/*@
requires n > 0;
*/
void foo0016(int n) {
 
  int i = 0;
  int k = 0;
  
  
  /*@
  ```c
  loop invariant 0 <= i <= n;
  loop invariant k == i;
  loop invariant 0 <= k <= n;
  loop invariant k == i && i <= n;
  loop invariant i - k == 0;
  ```
  loop invariant n > 0 ==> k >= 0;
  loop invariant n > 0 ==> i >= 0;
  loop invariant n - i == n - k;
  loop invariant k == i;
  loop invariant k == i && 0 <= k;
  loop invariant k <= n;
  loop invariant k <= i;
  loop invariant i == k;
  loop invariant i <= n;
  loop invariant \forall integer m; 0 <= m <= i ==> i <= n;
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
  loop invariant n > 0 ==> k >= 0;
  loop invariant n > 0 ==> k <= n;
  loop invariant n > 0 ==> j >= 0;
  loop invariant n - j > 0 ==> k > 0;
  loop invariant n - j <= k;
  loop invariant k == n - j;
  loop invariant k <= n;
  loop invariant k <= n - j;
  loop invariant k + j == n;
  loop invariant k + j <= n;
  loop invariant j == n - k;
  loop invariant j <= n;
  loop invariant j <= n - k;
  loop invariant \forall integer m; 0 <= m <= j ==> k + m <= n;
  loop invariant \forall integer m; 0 <= m < j ==> n - m > k;
  loop invariant \forall integer m; 0 <= m < j ==> n - m > 0;
  loop invariant \forall integer m; 0 <= m < j ==> k >= n - j;
  loop invariant 0 <= n - j;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= j + k;
  loop invariant 0 <= j && j <= n;
  loop assigns k;
  loop assigns j;
  */
  while( j < n ) {
    // @ assert k > 0;*/
    j++;
    k--;
  }
}
