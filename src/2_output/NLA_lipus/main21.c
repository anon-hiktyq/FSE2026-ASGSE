
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int main21() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
	int x = 0;
	int y = 0;


 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (((y == 0)&&(x == 0)) || (x == y * y) ) &&
(y >= 0
      loop assigns x, y)
    */
    
    while(unknown()) {
        y = y + 1;
        x = y * y;
    }

	
	return 0;
}