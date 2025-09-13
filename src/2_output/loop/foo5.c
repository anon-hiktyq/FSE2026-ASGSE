
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo5(int x, int y) 

            /*@
            Require x >= 0 && x <= 10 && y <= 10 && y >= 0
            Ensure Results(__return)
            */
            {
  
  
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= x@pre && y >= y@pre) &&
(x - y == x@pre - y@pre) &&
(x % 10 == x@pre % 10 && y % 10 == y@pre % 10) &&
(x == x@pre + 10 * ((x - x@pre) / 10)) &&
(y == y@pre + 10 * ((y - y@pre) / 10)
        loop assigns x, y
        loop variant 0 // unknown() does not guarantee termination)
    */
    
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }

    
    
  }