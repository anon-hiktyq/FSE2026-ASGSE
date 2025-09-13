
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int main25(int x,int w)

            /*@
            Require x >= 0
            Ensure Results(__return)
            */
            {
	
	int z = w * x;

	while(unknown())
	{
		w = w * x;
		z = z * x;
	}

	
	return 0;
}