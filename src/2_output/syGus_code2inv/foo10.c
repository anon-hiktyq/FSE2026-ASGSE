
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo10(int x,int y) 

            /*@
            Require x >= 0 && x <= 2 && y <= 2 && y >= 0
            Ensure Results(__return)
            */
            {

  
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= 0 && y >= 0) &&
(x <= 2 + 2 * ((y - y@pre) / 2) // Ensures x does not exceed the maximum possible value) &&
(y <= 2 + 2 * ((y - y@pre) / 2) // Ensures y does not exceed the maximum possible value) &&
((y == y@pre + 2 * ((y - y@pre) / 2)) && (x == x@pre + 2 * ((y - y@pre) / 2))
          loop assigns x, y)
    */
    
            while (unknown()) {
      
      x  = x + 2;
      y  = y + 2;

    }
      
  
  }