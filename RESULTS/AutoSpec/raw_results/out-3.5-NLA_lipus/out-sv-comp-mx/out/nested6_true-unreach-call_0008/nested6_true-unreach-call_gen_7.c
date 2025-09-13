#include <limits.h>
#include "assert.h"

int unknown1();

/*@
requires n < INT_MAX;
*/
int foo(int k, int n) {
    int i,j;
    //int k,n;
    if( k == n) {
    }
    else {
        goto END;
    }

    for (i = 0; i < n; i++) {
        /*@
        ```c
                /*@
                loop invariant 0 <= i <= n;
                loop invariant 0 <= j <= n;
                loop invariant j >= 2 * i;
                loop invariant \forall integer p, q; 0 <= p < i && 2 * p <= q < n ==> k >= j;
                loop assigns j, k;
                */
        ```
        */
        for (j= 2 * i; j < n; j++) {
            if(unknown1()) {
                /*@
                loop invariant k <= n;
                loop invariant j <= n;
                loop invariant j <= k;
                loop invariant j < n;
                loop invariant i >= 0 && j >= 2 * i;
                loop invariant i >= 0 && j >= 0 && k >= 0;
                loop invariant i < n;
                loop invariant \forall integer k; k <= n;
                loop invariant 2*i <= n;
                loop invariant 2*i <= k;
                loop invariant 2 * i <= k;
                loop invariant 2 * i <= j;
                loop invariant 0 <= k;
                loop invariant 0 <= j;
                loop invariant 0 <= i;
                loop assigns k;
                */
                for (k = j; k < n; k++) {
                    // @ assert k >= 2*i;
                }
            }
            else {
                // @ assert  k >= n ;
                // @ assert  k <= n ;
            }
        }
    }
END:
    return 0;
}