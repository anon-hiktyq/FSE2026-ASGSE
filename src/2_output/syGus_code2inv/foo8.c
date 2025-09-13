
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo8(int x, int y) 

            /*@
            Require x >= 0 && x <= 10 && y <= 10 && y >= 0
            Ensure Results(__return)
            */
            {
  
  
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= x && x <= 10 + 10 * ((x - x@pre) / 10) // Express x in terms of its initial value) &&
(0 <= y && y <= 10 + 10 * ((y - y@pre) / 10) // Express y in terms of its initial value) &&
((y == y@pre + 10 * ((x - x@pre) / 10)) // Relate y to its initial value) &&
((x == x@pre + 10 * ((x - x@pre) / 10)) // Relate x to its initial value
        loop assigns x, y)
    */
    
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }

    
    
  }