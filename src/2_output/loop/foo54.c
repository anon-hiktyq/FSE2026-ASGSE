
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo54(int x,int y) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {


  x = -50;
  
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while( x < 0 ) {
	x = x + y;
	y++;
  }
  
}