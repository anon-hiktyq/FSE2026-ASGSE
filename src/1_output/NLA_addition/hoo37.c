
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo37(int a, int b) 

            /*@
            Require a >= 0 && b >= 0
            Ensure Results(__return)
            */
            {
    
    int product = 0;  
    int i = 0;        

    
    while (i < b) {
        product = product + a;  
        i = i + 1;
    }

    
    
}