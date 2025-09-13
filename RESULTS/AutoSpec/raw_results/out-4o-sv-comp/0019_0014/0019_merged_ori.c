
#include <limits.h>

/*@
requires n <= INT_MAX;
*/
void foo0019(int n) {
  int i,k;
  k = n;
  i = 0;

  
  /*@
  loop invariant k == n - i/2;
  loop invariant k == n - i / 2;
  loop invariant k == n - (i / 2);
  loop invariant k <= n;
  loop invariant k <= n - i / 2;
  loop invariant k + i/2 == n;
  loop invariant i == 2 * (n - k);
  loop invariant i <= 2 * (n - k);
  loop invariant i % 2 == 0;
  loop invariant \forall integer m; 0 <= m < i/2 ==> 0 <= k <= n;
  loop invariant 0 <= i;
  loop assigns k;
  loop assigns i;
  */
  while( i < n ) {
    k--;
    i = i + 2;
  }

  int j = 0;

  
  /*@
  loop invariant n/2 - j <= k;
  loop invariant n/2 - j < k;
  loop invariant n / 2 - j <= k;
  loop invariant n - i / 2 - n / 2 <= k;
  loop invariant n - i / 2 - j <= k;
  loop invariant k == n - i / 2 - j;;
  loop invariant k <= n;
  loop invariant k <= n - j;
  loop invariant k <= n - i / 2;
  loop invariant k + j == n - i / 2;
  loop invariant k + j == (n - i / 2);
  loop invariant k + j <= n;
  loop invariant j <= n/2;
  loop invariant j <= n / 2;;
  loop invariant j <= n / 2;
  loop invariant j <= n - i / 2;
  loop invariant i == 2 * (n - k) - 2 * j;
  loop invariant i == 2 * (n - k - j);
  loop invariant i % 2 == 0;
  loop invariant \forall integer m; 0 <= m < j ==> k >= n - i / 2 - j;
  loop invariant \forall integer m; 0 <= m < j ==> k > m;
  loop invariant \forall integer m; 0 <= m < j ==> 0 <= k <= n - j;
  loop invariant \forall integer m; 0 <= m < j ==> 0 <= k <= n - i/2;
  loop invariant \forall integer m; 0 <= m < j ==> 0 <= k + m < n - m;
  loop invariant \forall integer l; 0 <= l < j ==> k - l > 0;
  loop invariant 2 * j <= i;
  loop invariant 0 <= k;
  loop invariant -1 < k;
  loop invariant k == n - i / 2 - j;
  loop invariant k == n - (i / 2) - j;
  loop invariant 0 <= j;
  loop assigns k;
  loop assigns j;
  */
  while( j < n/2 ) {
    // @ assert k > 0;
    k--;
    j++;
  }
}
