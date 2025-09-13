
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo23() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  
    int i=1;
    int j=20;
   
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (i % 2 == 1) &&
(j <= 20
      loop assigns i, j)
    */
    
    while (j >= i) {
      
      i = i + 2;
      j = j - 1;
      
    }
  
  
  }