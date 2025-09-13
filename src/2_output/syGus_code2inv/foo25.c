
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo25() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 10000;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= 0 // x is always non-negative) &&
(x + 0 == 10000 - (10000 - x) // x decreases from 10000 to 0
      loop assigns x // x is the only variable being modified in the loop)
    */
    
    while (x > 0) {
        x = x - 1;
    }
  
    
  }