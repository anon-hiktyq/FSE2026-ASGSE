#include <assert.h>

/*
  * "nested2.c" from InvGen benchmark suite
  */
/*@
requires l > 0;
*/
void foo(int l) {
  int i, k, n;

  for (k = 1; k < n; k++) {
    /*@
    loop invariant 1 <= k <= n;
    loop invariant l > 0;
    loop invariant \forall integer m; k <= m < n ==> m >= 1;
    loop assigns k;
    
    loop invariant l <= i <= n;
    loop invariant l > 0;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }
    for (i = l; i < n; i++) {
      // @ assert 1 <= k;
    }
  }

}