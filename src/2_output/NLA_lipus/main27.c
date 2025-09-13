
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main27(int x,int y) 

            /*@
            Require x >= 0 && y >= x
            Ensure Results(__return)
            */
            {
	
	int z=0;
	int w=0;


 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < y@pre) => (z == x * w)) &&
((0 < y@pre) => (0 <= w && w <= y@pre)) &&
((!(0 < y@pre)) => ((w == 0)&&(z == 0)&&(y == y@pre)&&(x == x@pre))) &&
(y == y@pre) &&
(x == x@pre
          loop assigns z, w)
    */
    
            while(w < y) {
		z += x;
		w += 1;
	}

	

	return 0;
}