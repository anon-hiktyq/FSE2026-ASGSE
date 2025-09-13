
#include <limits.h>

/*@
requires n <= INT_MAX;
*/
void foo0019(int n) {
  int i,k;
  k = n;
  i = 0;

  
  /*@
  loop invariant 0 <= i <= n;
  loop invariant k == n - i;
  loop invariant i % 2 == 0;
  loop assigns i, k;
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
}
