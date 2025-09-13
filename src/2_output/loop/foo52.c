
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo52()


            /*@
            Require emp
            Ensure Results(__return)
            */
            {
	int i = 1;
	int j = 0;
	int z = i - j;
	int x = 0;
	int y = 0;
	int w = 0;



 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (w == 2 * y) &&
(y >= 0
	  loop assigns z, x, y, w
	  loop variant y)
    */
    
	while(unknown()) 
	{
		z += x + y + w;
		y++;
		if (z % 2 == 1) 
		  x++;
		w += 2; 
	}

	
}