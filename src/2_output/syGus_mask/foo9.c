
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo9(int x,int y) 

            /*@
            Require x >= 0 && x <= 2 && y <= 2 && y >= 0
            Ensure Results(__return)
            */
            {

  
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((x >= 0 && x <= 2 && y >= 0 && y <= 2) => (x - y == x - y)) &&
((x >= 0 && x <= 2 && y >= 0 && y <= 2) => (x % 2 == x % 2)) &&
((x >= 0 && x <= 2 && y >= 0 && y <= 2) => (y % 2 == y % 2)
        loop assigns x, y)
    */
    
    while (unknown()) {
        x = x + 2;
        y = y + 2;
    }
  
  
    
  
  }