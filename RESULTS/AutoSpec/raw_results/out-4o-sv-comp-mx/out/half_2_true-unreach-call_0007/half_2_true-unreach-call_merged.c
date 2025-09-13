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
  loop invariant n % 2 == 1 ==> k % 2 == 1;
  loop invariant n % 2 == 0 ==> k % 2 == 0;
  loop invariant k == n - i;
  loop invariant k == n - i / 2;
  loop invariant i <= n;
  loop invariant \forall integer x; 0 <= x < i ==> x % 2 == 0;
  loop invariant \forall integer x; 0 <= x < i / 2 ==> n - x == k;
  loop invariant 0 <= k;
  loop invariant (n - i) % 2 == 0;
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