
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


 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((x@pre * x@pre <= 1000) => (y == x@pre * x@pre + (x - x@pre)) ) &&
((x@pre * x@pre <= 1000) => (x >= x@pre) ) &&
((x@pre * x@pre <= 1000) => (y <= x * x) ) &&
((x@pre * x@pre <= 1000) => (y <= 1000 + 2*x + 1) ) &&
((x@pre * x@pre <= 1000) => (x * x > 1000 => y <= 1000) ) &&
((!(x@pre * x@pre <= 1000)) => ((y == x@pre * x@pre)&&(x == x@pre))
          loop assigns x, y)
    */
    
            while(x * x <= 1000) {
		x = x + 1;
		y = y + 1;
	}

	
	return 0;
}