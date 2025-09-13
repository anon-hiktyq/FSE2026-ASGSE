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
    loop invariant k > 0;
    loop assigns k, i;
    loop invariant l > 0;
    loop invariant \forall integer j; 1 <= j < k ==> \forall integer m; l <= m < n ==> true;
    */
    for (i = l; i < n; i++) {

    }
    for (i = l; i < n; i++) {
      // @ assert 1 <= k;
    }
  }

}