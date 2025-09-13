
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0014(int n) 

            /*@
            Require 0 <= n && n < 1000
            Ensure Results(__return)
            */
            {

    int i=0;
    int sn=0;
    
   
    for (i = 1; i <= n; i++) {
        sn = sn + (2);
    }
    
    
}