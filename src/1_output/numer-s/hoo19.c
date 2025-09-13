
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo19()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 0;
    int y = 500000;

    //loop-body
    while(x < 1000000) {
	    if (x < 500000) {
	        x = x + 1;
	    } 
        else {
            x = x + 1;
            y = y + 1;
	    }
    }

    //post-condition
    
}