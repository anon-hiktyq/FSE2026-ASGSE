
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo15()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 0;
    int y = 0;

  

    //loop-body
    while (unknown()) {
        x += 4;
        y++;
    }

    //post-condition
    
}