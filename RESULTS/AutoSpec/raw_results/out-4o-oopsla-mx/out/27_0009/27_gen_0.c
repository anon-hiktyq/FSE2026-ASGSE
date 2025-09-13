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
    loop invariant 0 < k <= n;
    loop invariant \forall integer i; l <= i < n ==> \exists integer j; 1 <= j <= k;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }
    for (i = l; i < n; i++) {
      // @ assert 1 <= k;
    }
  }

}