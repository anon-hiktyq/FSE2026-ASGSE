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
  loop invariant n - i <= k;
  loop invariant n % 2 == 0 ==> (n - i) % 2 == 0;
  loop invariant k == n - i/2;
  loop invariant k == n - i / 2;
  loop invariant k <= n;
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
  loop invariant k == n - j;
  loop invariant j <= n / 2;
  loop invariant k > n / 2 - j;
  loop invariant k <= n;
  loop invariant 0 <= j <= n / 2;
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