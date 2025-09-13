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
  loop invariant n - i / 2 <= k <= n;
  loop invariant k == n - i / 2;
  loop invariant 0 <= i <= 2 * n;
  loop assigns k;
  loop assigns i;
  
  loop invariant k == n - i / 2 - j;
  loop invariant 0 <= j <= n / 2;
  loop invariant k >= 0;
  loop assigns k;
  loop assigns j;
  loop invariant k == n - i/2;
  loop invariant k == n - \floor(i / 2);
  loop invariant k == n - (i / 2);
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
  return 0;
}