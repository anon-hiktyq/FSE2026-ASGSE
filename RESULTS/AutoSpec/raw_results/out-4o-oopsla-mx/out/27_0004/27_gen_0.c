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
    loop invariant k <= n;
    loop invariant i <= n;
    loop invariant \forall integer x; l <= x < n ==> (x >= l);
    loop invariant \forall integer x; l <= x < i ==> \forall integer y; 1 <= y < k;
    loop invariant \forall integer m; l <= m < i ==> m >= l && m < n;
    loop invariant 1 <= k;
    loop invariant 0 < l;
    loop assigns i;
    */
    for (i = l; i < n; i++) {

    }
    /*@
    ```c
    loop invariant l <= i;
    loop invariant k <= n;
    loop invariant i <= n;
    loop invariant 1 <= k;
    loop invariant 0 < l;
    loop invariant \forall integer m; l <= m < i ==> m >= l && m < n;
    loop assigns i;
    ```
    */
    for (i = l; i < n; i++) {
      // @ assert 1 <= k;
    }
  }

}