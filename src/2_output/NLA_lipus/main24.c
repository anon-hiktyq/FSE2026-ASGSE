
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main24(int x,int y) 

            /*@
            Require x >= 0 && y >= 0
            Ensure Results(__return)
            */
            {
	
	int z = x * y;


 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((x@pre > 0) => (x >= 0)) &&
((x@pre > 0) => (z == x@pre * y@pre - (x@pre - x) * y@pre)) &&
((!(x@pre > 0)) => ((z == x@pre * y@pre)&&(y == y@pre)&&(x == x@pre))) &&
(y == y@pre
          loop assigns x, z)
    */
    
            while(x > 0) {
		x = x - 1;
		z = z - y;
	}

	
	return 0;
}