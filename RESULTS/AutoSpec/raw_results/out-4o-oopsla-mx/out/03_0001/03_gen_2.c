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
    ```c
    loop invariant 1 <= k <= n;
    loop invariant l <= i <= n;
    loop invariant l > 0;
    loop invariant n > l;
    loop assigns k, i;
    loop invariant i == l; // ensures the inner loop starts with i == l
    loop invariant n > k; // Ensures `k` value upper bounds 
    loop invariant asserts carries 
    ```
    */
    for (i=l; i<n; i++) {
    }
    for (i=l; i<n; i++) {
      // @ assert 1<=i;
    }
  }

}
