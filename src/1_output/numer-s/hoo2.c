
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo2()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    //pre-condiiton
    int x =5;
   
    //loop-body
    while(unknown()){
        x = x + 8;
    }

    //post-condition
    
}