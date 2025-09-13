
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void  foo56(int k) 

            /*@
            Require 0 <= k && k <= 1
            Ensure Results(__return)
            */
            {
    int i,j;
    i = 1;
    j = 1;
   

    while (i < 1000000) {
        i = i + 1;
        j = j + k;
        k = k - 1;
        
    }
    
}