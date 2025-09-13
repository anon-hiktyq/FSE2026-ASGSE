
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo1()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  
    int x = 1;
    int y = 0;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x == 1 + (y * (y - 1)) / 2) &&
(0 <= y && y <= 100000
      loop assigns x, y
      loop variant 100000 - y)
    */
    
    while (y < 100000) {
      
       x = x + y;
       y = y + 1;
    }
  
    
  }