#include <limits.h>
#include "assert.h"

int unknown1();

/*@
requires l > 0;
requires l < INT_MAX;
requires n < INT_MAX;
*/
void foo(int n, int l) {
  int i,k;
  //int n,l;
  /*@
  ```c
  loop invariant 1 <= k <= n;
  loop invariant l > 0 && l < INT_MAX;
  loop invariant n < INT_MAX;
  loop invariant l <= i <= n;
  loop invariant \forall integer m; l <= m < i ==> 1 <= m;
  loop invariant \forall integer m; 1 <= m < k ==> l <= n;
  loop assigns i, l, k;
  ```
  */
  for (k = 1; k < n; k++){
    /*@
    loop invariant n < INT_MAX;
    loop invariant l > 0 && l < INT_MAX;
    loop invariant l <= i;
    loop invariant l < INT_MAX;
    loop invariant k <= n;
    loop invariant i <= n;
    loop invariant \forall integer m; l <= m < n ==> 1 <= m;
    loop invariant \forall integer m; l <= m < i ==> 1 <= m;
    loop invariant \forall integer m; 1 <= m < k ==> l <= n;
    loop invariant \forall integer i; 1 <= i < l ==> i < n;
    loop invariant 1 <= k;
    loop invariant 1 <= i;
    loop invariant 0 < l;
    loop assigns i;
    */
    for (i = l; i < n; i++){  
      // @ assert 1 <= i;
    }
    if(unknown1()) {
      l = l + 1;
    }
  }
 }