
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo11(int y)

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 0;

    //pre-condition
    
    //loop-body
    while (x < 99) {
        if (y % 2 == 0) 
            x += 10;
        else 
            x -= 5;
    }

    //post-condition
    
}