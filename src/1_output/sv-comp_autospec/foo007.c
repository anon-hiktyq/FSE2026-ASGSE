
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo007(int n) 

            /*@
            Require 0 < n
            Ensure Results(__return)
            */
            {
    int k = 0;
    int i = 0;


    while (i < n) {
        i++;
        k++;
    }
    int j = n;


    while (j > 0) {
        j--;
        k--;
        
    }


}