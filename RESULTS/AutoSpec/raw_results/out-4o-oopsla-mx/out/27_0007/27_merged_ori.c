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
    loop invariant l <= i;
    loop invariant l < n;
    loop invariant k <= n;
    loop invariant k < n;
    loop invariant i == n || i == l;
    loop invariant i <= n;
    loop invariant \forall integer m; l <= m < i ==> 1 <= k;
    loop invariant \forall integer m; 0 <= m < k ==> 1 <= m;
    loop invariant \forall integer j; l <= j <= i ==> 1 <= k;
    loop invariant \forall integer j; l <= j < n ==> \exists integer m; 1 <= m < n;
    loop invariant 1 <= k;
    loop invariant 0 <= l;
    loop invariant 0 < l;
    loop assigns i;
    ```c;
    ```;
    */
    for (i = l; i < n; i++) {

    }
    for (i = l; i < n; i++) {
      // @ assert 1 <= k;
    }
  }

}