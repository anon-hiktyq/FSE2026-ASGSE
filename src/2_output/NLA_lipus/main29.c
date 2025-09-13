
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main29(int x,int y,int n) 

            /*@
            Require x >= 0 && y >= 0 && n >= 0
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
    (0 <= n && n <= n@pre) &&
(z == (n@pre - n) * (x * x)) &&
(w == (n@pre - n) * (y * y)) &&
(p == (n@pre - n) * (x * y)
            loop assigns z, w, p, n)
    */
    
        
            while(n > 0) {
		z = z + x * x;
		w = w + y * y;
		p = p + x * y;
		n -= 1;
	}
    // post-condition
	
}