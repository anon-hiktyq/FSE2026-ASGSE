
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo86(int y,int z1,int z2,int z3) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    int x = -50;
  
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (y >= y@pre) &&
(y > 0 || x < 0 // Ensure y will eventually become positive
            loop assigns x, y
            loop variant x + 50)
    */
    
            while (x < 0) {
      
      x  = x + y;
      y  = y + 1;
      
  
    }
    
  
  }