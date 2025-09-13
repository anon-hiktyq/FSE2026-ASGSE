#include <assert.h>

/*
 * "nested4.c" from InvGen benchmark suite
 */

/*@
requires l > 0;
requires n > l;
*/
void foo(int n, int l) {
  int i,k;


  for (k=1; k<n; k++){
    /*@
    loop invariant l <= n;
    loop invariant l <= i;
    loop invariant l < n;
    loop invariant k <= n;
    loop invariant i <= n;
    loop invariant \forall integer m; l <= m < i ==> 1 <= m;
    loop invariant \forall integer j; l <= j < i ==> 1 <= j;
    loop invariant 1 <= l;
    loop invariant 1 <= k;
    loop invariant 1 <= i;
    loop invariant 0 < k;
    loop assigns i;
    */
    for (i=l; i<n; i++) {
    }
    /*@
    loop invariant l <= n;
    loop invariant l <= i;
    loop invariant k <= n;
    loop invariant i <= n;
    loop invariant \forall integer m; l <= m < i ==> 1 <= m;
    loop invariant \forall integer j; l <= j < i ==> 1 <= j;
    loop invariant 1 <= l;
    loop invariant 1 <= k;
    loop invariant 1 <= i;
    loop invariant 0 < k;
    loop assigns i;
    */
    for (i=l; i<n; i++) {
      // @ assert 1<=i;
    }
  }

}
