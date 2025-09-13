
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo10()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    //pre-condition
    int x = 1;
    int y = 0;
    
    //loop-body
    while (y < 1024) {
        x = 0;
        y = y + 1;
    }

    //post-condition
    
}