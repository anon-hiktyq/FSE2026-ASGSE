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
  loop invariant n < INT_MAX;
  loop invariant l > 0 && l < INT_MAX;
  loop invariant l <= n;
  loop invariant l < INT_MAX;
  loop invariant k <= n;
  loop invariant k < INT_MAX;
  loop invariant \forall integer i; l <= i < n ==> 1 <= i;
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns k;
  loop assigns l;
  loop assigns i;
  */
  for (k = 1; k < n; k++){
    /*@
    loop invariant n < INT_MAX;
    loop invariant l > 0 && l < INT_MAX;
    loop invariant l <= n;
    loop invariant l < INT_MAX;
    loop invariant k <= n;
    loop invariant k < INT_MAX;
    loop invariant \forall integer j; l <= j < i ==> 1 <= j;
    loop invariant \forall integer j; 1 <= j < k ==> l <= n;
    loop invariant \forall integer i; l <= i < n ==> 1 <= i;
    loop invariant 1 <= k;
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