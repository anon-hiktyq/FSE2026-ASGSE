
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0013(int n, int m , int l) 

            /*@
            Require INT_MIN < n && n < INT_MAX && INT_MIN < m && m < INT_MAX && INT_MIN < l && l < INT_MAX && 3*n <= m + l
            Ensure Results(__return)
            */
            {
    int i, j, k;

    i = 0;
    for (i = 0; i < n; i++) {
        j = 2 * i;
        for (j = 2 * i; j < 3 * i; j++) {
            k = i;
            
            for (k = i; k < j; k++) {
                
            }
        }
    }
}