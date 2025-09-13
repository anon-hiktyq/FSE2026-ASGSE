
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
        loop invariant 2 * i <= j;
        loop invariant j < 3 * i;
        loop invariant 0 <= i < n;
        loop invariant 0 <= j; 
        loop invariant i <= j / 2;
        loop assigns j;
        loop assigns k;
        */
        for (j = 2 * i; j < 3 * i; j++) {
            k = i;
            
            /*@
            loop invariant k <= j;
            loop invariant k - i <= j - i;
            loop invariant k - i <= 2*n;
            loop invariant k - i <= 2 * n;
            loop invariant k - i <= 2 * i;
            loop invariant j <= 3*i;
            loop invariant j <= 3 * i;
            loop invariant j < 3*i;
            loop invariant j < 3 * i;
            loop invariant i <= n;
            loop invariant i <= k;
            loop invariant i <= j;
            loop invariant i < n;
            loop invariant \forall integer x; i <= x < k ==> x - i <= 2 * n;
            loop invariant 2*i <= j;
            loop invariant 2 * i <= k;
            loop invariant 2 * i <= j;
            loop invariant 0 <= k;
            loop invariant 0 <= i;
            loop invariant 0 <= 2*i;
            loop assigns k;
            */
            for (k = i; k < j; k++) {
                // @ assert k - i <= 2 * n;
            }
        }
    }
}
