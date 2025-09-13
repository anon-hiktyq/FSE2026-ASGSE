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
  loop invariant 1 <= k <= n;
  loop invariant 0 < l < INT_MAX;
  loop invariant l <= n;
  loop assigns k, l;
  */
  for (k = 1; k < n; k++){
    /*@
    loop invariant n < INT_MAX;
    loop invariant l > 0 && l < INT_MAX;
    loop invariant l <= i;
    loop invariant l < n;
    loop invariant l < INT_MAX;
    loop invariant k <= n;
    loop invariant k < n;
    loop invariant i <= n;
    loop invariant 1 <= l;
    loop invariant 1 <= k;
    loop invariant 0 <= k;
    loop invariant 0 <= i;
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