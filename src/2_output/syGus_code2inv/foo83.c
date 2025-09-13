
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo83(int y) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    int x = -5000;
  
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while (x < 0) {
      
      x  = x + y;
      y  = y + 1;
      
  
    }
    
  
  }