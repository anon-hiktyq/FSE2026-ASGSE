
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo14() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  
    int i=1;
    int j=10;
   
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (j + i == 11 + (i - 1) / 2) &&
(i % 2 == 1) &&
(j >= 6
      loop assigns i, j)
    */
    
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
  
    
  
  }