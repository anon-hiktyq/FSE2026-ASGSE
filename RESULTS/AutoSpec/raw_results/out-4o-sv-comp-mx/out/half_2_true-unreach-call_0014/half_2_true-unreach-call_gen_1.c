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
  loop invariant 0 <= i <= n;
  loop invariant k == n - (i / 2);
  loop assigns i, k;
  
  loop invariant 0 <= j <= n / 2;
  loop invariant k == n / 2 - j;
  loop assigns j, k;
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