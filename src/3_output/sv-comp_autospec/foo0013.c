
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
    
            
            /*@
          loop invariant (!(0 < \at(n,Pre))) ==> ((i == 0)&&(l == \at(l,Pre))&&(m == \at(m,Pre))&&(n == \at(n,Pre)));
            */
            for (i = 0; i < n; i++) {
        j = 2 * i;
        
            
            /*@
            */
            for (j = 2 * i; j < 3 * i; j++) {
            k = i;
            
            
            
            /*@
            loop invariant i <= k <= j;
            */
            for (k = i; k < j; k++) {
                /*@ assert k - i <= 2 * n; */
            }
            
        }
            
    }
            
}
