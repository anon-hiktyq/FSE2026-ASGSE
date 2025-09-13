
#include <limits.h>

/*@
requires n <= INT_MAX;
*/
void foo0019(int n) {
  int i,k;
  k = n;
  i = 0;

  
  /*@
  loop invariant n - i <= k;
  loop invariant k == n - i;
  loop invariant k == n - i/2;
  loop invariant k == n - i / 2;
  loop invariant k <= n;
  loop invariant k + i == n;
  loop invariant j <= n / 2;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i / 2 <= k;
  loop invariant i / 2 <= j;
  loop invariant i / 2 + j <= n / 2;
  loop invariant 2 * k + i == 2 * n;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant i % 2 == 0;
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
