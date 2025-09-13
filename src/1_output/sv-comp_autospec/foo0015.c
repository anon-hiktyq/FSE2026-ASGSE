
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0015(int x, int y) 

            /*@
            Require y <= 1000000
            Ensure Results(__return)
            */
            {

	if (y > 0) {
		
		while (x < 100) {
			x = x + y;
		}
	}

	
}