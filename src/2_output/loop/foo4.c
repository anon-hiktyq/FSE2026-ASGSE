
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo4(int x, int y) 

            /*@
            Require x >= 0 && x <= 10 && y <= 10 && y >= 0
            Ensure Results(__return)
            */
            {
  
  
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= 0 && y >= 0) &&
(x - y == x@pre - y@pre
        loop assigns x, y
        loop variant x + y)
    */
    
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }

    
  
   
  }