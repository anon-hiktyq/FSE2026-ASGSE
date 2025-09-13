
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo16()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 0;
    int y = 0;
    int z = 0;

   
    //loop-body
    while (x > 0) {
        x++;
        y++;
        z -= 2;
    }

    //post-condition
    
}