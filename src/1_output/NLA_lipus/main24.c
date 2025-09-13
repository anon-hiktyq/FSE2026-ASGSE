
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

	while(x > 0) {
		x = x - 1;
		z = z - y;
	}

	
	return 0;
}