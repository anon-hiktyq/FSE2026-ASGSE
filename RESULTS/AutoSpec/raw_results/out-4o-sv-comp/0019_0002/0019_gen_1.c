
#include <limits.h>

/*@
requires n <= INT_MAX;
*/
void foo0019(int n) {
  int i,k;
  k = n;
  i = 0;

  
  /*@
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
  ```c
  /*@
  loop invariant 0 <= j <= n/2;
  loop invariant k == n - 2*j;
  loop invariant k > 0;
  loop assigns j;
  loop assigns k;
  */
  ```
  */
  while( j < n/2 ) {
    // @ assert k > 0;
    k--;
    j++;
  }
}
