
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo02() 
/*@

Require emp

Ensure emp
*/{
	int i = 1;
	int j = 0;
	int z = i - j;
	int x = 0;
	int y = 0;
	int w = 0;



 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x == y) &&
(z % 2 == 1) &&
(w == 2*y) &&
(0 <= y && y <= x
	loop assigns x
	loop assigns y
	loop assigns w
	loop assigns z)
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