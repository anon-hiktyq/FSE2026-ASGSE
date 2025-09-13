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
        loop invariant k == n || k >= 0;
        loop invariant k == n || k == j;
        loop invariant k == n || k < n;
        loop invariant k == n || k != n;
        loop invariant k <= n;
        loop invariant j <= n;
        loop invariant i >= 0 && j >= 2 * i;
        loop invariant i <= n;
        loop invariant i < n;
        loop invariant \forall integer y; 0 <= y <= j ==> (y >= 2 * i);
        loop invariant \forall integer x; 0 <= x < i ==> \forall integer y; 2 * x <= y < n ==> (k == n || k >= y);
        loop invariant \forall integer x; 0 <= x < i ==> (2 * x < n);
        loop invariant \forall integer x, y; 0 <= x < i && 2 * x <= y < n ==> k >= 2 * x;
        loop invariant \forall integer x, y; (0 <= x < i && 2 * x <= y < n) ==> (k == n || 2 * x <= k);
        loop invariant \forall integer p, q; 0 <= p < i && 2 * p <= q < n ==> k >= j;
        loop invariant 2 * i <= n;
        loop invariant 2 * i <= j;
        loop invariant 0 <= k;
        loop invariant 0 <= j;
        loop invariant 0 <= i;
        loop assigns k;
        loop assigns j;
        loop assigns i;
        ```c;
        ```;
        /*@;
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