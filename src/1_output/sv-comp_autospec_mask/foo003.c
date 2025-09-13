
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int foo003(int n) 

            /*@
            Require 0 <= n && n < 1000000
            Ensure Results(__return)
            */
            {
    int i = 0; 
    int a = 0; 
    int b = 0; 
    
   
    while (i < n) {
        if (unknown1()) {
            a = a + 1;
            b = b + 2;
        } else {
            a = a + 2;
            b = b + 1;
        }
        i = i + 1;
    }

    
    
    return 0;
}