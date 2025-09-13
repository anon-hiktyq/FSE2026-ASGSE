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
  for (k = 1; k < n; k++){
    /*@
    loop invariant 0 <= k < n;
    loop assigns k;
    loop assigns l;
    loop invariant l > 0;
    loop invariant l < n;
    loop invariant l <= INT_MAX;
    loop invariant n <= INT_MAX;
    
    loop invariant k >= 1;
    loop invariant 0 <= i <= n;
    loop invariant i >= l;
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