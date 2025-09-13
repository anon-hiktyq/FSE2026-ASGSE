
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

	while(w < y) {
		z += x;
		w += 1;
	}

	

	return 0;
}