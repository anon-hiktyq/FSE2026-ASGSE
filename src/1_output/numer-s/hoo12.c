
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo12(int y)

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    //pre-condition
    int x = 0;
    
    //loop-body
    while (x < 99) {
        if(y % 2 == 0){
            x = x + 2;
        } 
        else{
            x = x + 1;
        }
    }

    //post-condition
    
}