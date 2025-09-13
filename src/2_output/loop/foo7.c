
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo7(int x,int y) 

            /*@
            Require x >= 0 && x <= 2 && y <= 2 && y >= 0
            Ensure Results(__return)
            */
            {

  
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= 0 && y >= 0) &&
(x - y == x@pre - y@pre) &&
(x % 2 == x@pre % 2) &&
(y % 2 == y@pre % 2) &&
(x == x@pre + 2 * ((x - x@pre) / 2)) &&
(y == y@pre + 2 * ((y - y@pre) / 2)
            loop assigns x, y
            loop variant 0 // Non-deterministic termination)
    */
    
        while (unknown()) {
            x = x + 2;
            y = y + 2;
        }
      
  
  }