
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int foo0021(int k, int n) 

            /*@
            Require n < INT_MAX && k == n
            Ensure Results(__return)
            */
            {
    int i,j;

    i = 0;

    for (; i < n; i++) {
        
        j = 2*i;
        
        for (; j < n; j++) {
            if(unknown1()) {
                
               
            }
            else {
                
            }
        }
    }
}