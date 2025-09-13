
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
		
	
 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (!(x@pre < 100) => (y == y@pre && x == x@pre)) &&
(y == y@pre
            loop assigns x)
    */
    
        while (x < 100) {
            x = x + y;
        }
	}

	
}