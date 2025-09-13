
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo04(int x,int y) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {


  x = -50;
  
  while( x < 0 ) {
	x = x + y;
	y++;
  }
  
}