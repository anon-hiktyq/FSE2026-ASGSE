
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo9()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    //pre-condition
    int x = 1;

    //loop-body
    while(unknown()){
        x = x + 2;
    }

    //post-condition
    
    
}