
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main30(int x,int y,int n) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body
	while(n > 0) {
		z = z + x * x;
		w = w + y * y;
		p = p + x * y;
		n -= 1;
	}
    // post-condition
	
}