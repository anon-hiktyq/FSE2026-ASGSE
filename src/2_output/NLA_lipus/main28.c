
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main28(int x,int y) 

            /*@
            Require x >= 0 && y >= x
            Ensure Results(__return)
            */
            {
    // variable declarations
	
	int z=0;
	int w=0;
	int p=0;
    
    // loop body

 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < y@pre) => (z == w * x)) &&
((0 < y@pre) => (w >= 0 && w <= y@pre)) &&
((0 < y@pre) => (p == x * (1 + w) * w / 2)) &&
((!(0 < y@pre)) => ((p == 0)&&(w == 0)&&(z == 0)&&(y == y@pre)&&(x == x@pre))) &&
(y == y@pre) &&
(x == x@pre
          loop assigns z, w, p)
    */
    
            while(w < y) {
		z += x;
		p += z;
		w += 1;
	}
    // post-condition
	

	return 0;
}