
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo36(int n) 

            /*@
            Require n > 0
            Ensure Results(__return)
            */
            {
    
    int sum = 0;   
    int i = 1;     

    
    while (i <= n) {
        sum = sum + i;  
        i = i + 1;      
    }

    
    
    
}