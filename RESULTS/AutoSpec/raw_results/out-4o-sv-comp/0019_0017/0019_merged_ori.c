
#include <limits.h>

/*@
requires n <= INT_MAX;
*/
void foo0019(int n) {
  int i,k;
  k = n;
  i = 0;

  
  /*@
  loop invariant n - i/2 == k;
  loop invariant k == n - i/2 - j;
  loop invariant k == n - i / 2 - j;
  loop invariant k == (n - i/2) - j;
  loop invariant k <= n - j;
  loop invariant k <= n - i/2;
  loop invariant j <= n/2;
  loop invariant j <= n / 2;
  loop invariant j <= k;
  loop invariant i/2 <= n;
  loop invariant i <= n;
  loop invariant i <= 2*n;
  loop invariant i <= 2*k;
  loop invariant \forall integer m; 0 <= m < n/2 ==> (m < j);
  loop invariant \forall integer m; 0 <= m < n ==> (m % 2 == 0);
  loop invariant \exists integer m; 0 <= m < n/2 && (m == j);
  loop invariant \exists integer m; 0 <= m < n && (m % 2 == 0);
  loop invariant 2*n - 2*i == 2*k;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant -n/2 < k;
  loop invariant k == n - i/2;
  loop invariant k == n - i / 2;
  loop invariant k <= n;
  loop invariant i % 2 == 0;
  loop invariant 0 <= i;
  loop invariant (i % 2) == 0;
  loop assigns k;
  loop assigns i;
  */
  while( i < n ) {
    k--;
    i = i + 2;
  }

  int j = 0;

  
  /*@
  loop invariant k == n - i/2 - j;
  loop invariant k == n - i / 2 - j;
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
