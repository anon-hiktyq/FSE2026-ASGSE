
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo32(int x) 

            /*@
            Require x >= 0 && x <= 10
            Ensure Results(__return)
            */
            {
	
	int y = x * x;

	while(x * x <= 1000) {
		x = x + 1;
		y = y + 1;
	}

	
	return 0;
}