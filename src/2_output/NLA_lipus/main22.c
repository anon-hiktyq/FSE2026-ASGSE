
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int main22(int x) 

            /*@
            Require x >= 0
            Ensure Results(__return)
            */
            {
	
	int y = x * x;


 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (y <= x * x) &&
(x >= x@pre // x is at least the initial value) &&
(y == x@pre * x@pre + (x - x@pre)
          loop assigns x, y)
    */
    
            while(unknown()) {
		x = x + 1;
		y = y + 1;
	}

	
	return 0;
}