
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo14(int k)

            /*@
            Require k >= 0 && k <= 1
            Ensure Results(__return)
            */
            {
    int i = 1;
    int j = 1;

    //pre-condition
    //loop-body
    while (unknown()) {
        i = i + 1;
        j = j + k;
        k = k - 1;
    }

    //post-condition
    
}