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
  loop invariant k + i / 2 == n;
  loop invariant k >= 0;
  loop invariant i <= n;
  loop invariant i % 2 == 0;
  loop invariant \forall integer m; 0 <= m < i / 2 ==> k == n - m;
  
  loop invariant k + i / 2 + j == n;
  loop invariant j <= n / 2;
  loop invariant j >= 0;
  loop invariant k >= 0;
  loop invariant \forall integer l; 0 <= l < j ==> k == n - i / 2 - l;
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