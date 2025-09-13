
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
        loop invariant k == i;
        loop invariant k <= j;
        loop invariant k <= 3 * i;
        loop invariant k < 3 * i;
        loop invariant j == 2 * i;
        loop invariant j <= 3*i;
        loop invariant j <= 3 * i;
        loop invariant j < 3 * i;
        loop invariant i <= n;
        loop invariant i <= k;
        loop invariant i <= j / 2;
        loop invariant i < n;
        loop invariant \forall integer x; i <= x < n ==> 2 * x <= 3 * x;
        loop invariant \forall integer x; i <= x < k ==> k - x <= 2 * n;
        loop invariant \forall integer x; 2 * i <= x < j ==> k - x <= 2 * n;
        loop invariant \forall integer x; 0 <= x < i ==> 2*x <= j <= 3*x;
        loop invariant \forall integer x; 0 <= x < i ==> 2*x <= j < 3*x;
        loop invariant \forall integer x; 0 <= x < i ==> 2*x <= j && j <= 3*x;
        loop invariant \forall integer x; 0 <= x < i ==> 2 * x <= 3 * x;
        loop invariant INT_MIN < k && k < INT_MAX;
        loop invariant 2*i <= j;
        loop invariant 2 * i <= m;
        loop invariant 2 * i <= l;
        loop invariant 2 * i <= j;
        loop invariant 0 <= k;
        loop invariant 0 <= j;
        loop invariant 0 <= i;
        loop assigns k;
        loop assigns j;
        loop assigns i;
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
