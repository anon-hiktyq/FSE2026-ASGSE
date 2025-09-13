
#include <limits.h>
#include "assert.h"

/*@
requires INT_MIN < n && n < INT_MAX;
requires INT_MIN < m && m < INT_MAX;
requires INT_MIN < l && l < INT_MAX;
requires 3*n <= m + l;
*/
void foo0013(int n, int m , int l) {
    int i, j, k;

    i = 0;
    for (i = 0; i < n; i++) {
        j = 2 * i;
        /*@
        ```c
        /*@ 
        loop invariant 0 <= i <= n;
        loop invariant 2*i <= j <= 3*i;
        loop invariant \forall integer x; 0 <= x < i ==> 2*x <= j < 3*x;
        loop assigns i, j, k;
        */
        ```
        */
        for (j = 2 * i; j < 3 * i; j++) {
            k = i;
            
            /*@
            loop invariant k <= j;
            loop invariant k < j;
            loop invariant k < INT_MAX;
            loop invariant k - i <= 2*n;
            loop invariant k - i <= 2 * n;
            loop invariant j <= 3*i;
            loop invariant j <= 3 * i;
            loop invariant j < 3*i;
            loop invariant j < 3 * i;
            loop invariant i <= k;
            loop invariant i <= j;
            loop invariant i < n;
            loop invariant i < j;
            loop invariant \forall integer x; i <= x < k ==> k - x <= 2 * n;
            loop invariant INT_MIN < k;
            loop invariant 2*i <= j;
            loop invariant 2 * i <= j;
            loop invariant 0 <= i;
            loop assigns k;
            */
            for (k = i; k < j; k++) {
                // @ assert k - i <= 2 * n;
            }
        }
    }
}
