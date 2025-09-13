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
    loop invariant \forall integer j; l <= j < n ==> \forall integer m; 1 <= m < k;
    loop assigns k;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }
    for (i = l; i < n; i++) {
      // @ assert 1 <= k;
    }
  }

}