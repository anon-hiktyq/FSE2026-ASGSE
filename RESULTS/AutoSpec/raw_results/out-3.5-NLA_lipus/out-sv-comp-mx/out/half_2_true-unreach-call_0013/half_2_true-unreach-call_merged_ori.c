#include <limits.h>
#include "assert.h"

/*@
requires n <= INT_MAX;
*/
int foo(int n) {
  int i,k;
  k = n;
  i = 0;

  /*@
  loop invariant n / 2 - j <= k;
  loop invariant n - i / 2 == k;
  loop invariant n % 2 == 0 ==> i <= n;
  loop invariant k == n - i / 2 - j;
  loop invariant k <= n;
  loop invariant k + j == n - i / 2;
  loop invariant k + i / 2 == n;
  loop invariant k + i / 2 + j == n;
  loop invariant j <= n / 2;
  loop invariant j <= k;
  loop invariant i <= n;
  loop invariant i <= 2 * n;
  loop invariant i <= 2 * k;
  loop invariant i <= 2 * (n - k);
  loop invariant \forall integer x; 0 <= x < j ==> k == n - i / 2 - x;
  loop invariant \forall integer x; 0 <= x < i/2 ==> k == n - x;
  loop invariant \forall integer x; 0 <= x < i / 2 ==> k == n - x;
  loop invariant \forall integer m; 0 <= m <= i/2 ==> k == n - m;
  loop invariant \forall integer m; 0 <= m < i / 2 ==> k == n - m;
  loop invariant \forall integer l; 0 <= l < j ==> k == n - i / 2 - l;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= j && j <= n / 2;
  loop invariant 0 <= i && i <= n;
  loop invariant k == n - i/2;
  loop invariant k == n - i / 2;
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
  loop invariant k == n - i / 2 - j;
  loop invariant i % 2 == 0;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns k;
  loop assigns j;
  */
  while( j < n/2 ) {
    // @ assert k > 0;
    k--;
    j++;
  }
  return 0;
}