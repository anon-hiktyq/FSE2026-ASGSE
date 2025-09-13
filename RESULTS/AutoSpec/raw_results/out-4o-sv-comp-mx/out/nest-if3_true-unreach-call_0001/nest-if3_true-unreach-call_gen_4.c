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
    loop invariant 1 <= k <= n;
    loop invariant l > 0 && l < INT_MAX;
    loop invariant n < INT_MAX;
    loop invariant \forall integer i; 1 <= i < l ==> i < n;
    loop assigns k, l;
    */
    for (i = l; i < n; i++){  
      // @ assert 1 <= i;
    }
    if(unknown1()) {
      l = l + 1;
    }
  }
 }