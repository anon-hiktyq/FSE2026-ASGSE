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
  loop invariant k == n - i;
  loop invariant k == n - i - j;
  loop invariant j <= n/2;
  loop invariant i <= n;
  loop invariant i % 2 == 0;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 < k;
  loop assigns k;
  loop assigns j;
  loop assigns i;
  */
  while( i < n ) {
    k--;
    i = i + 2;
  }

  int j = 0;
 
  while( j < n/2 ) {
    // @ assert k > 0;
    k--;
    j++;
  }
  return 0;
}