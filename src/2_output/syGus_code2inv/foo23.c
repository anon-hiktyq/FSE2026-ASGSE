
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
    (j == 20 - (i - 1) / 2) &&
(i == 1 + 2 * (20 - j)) &&
(j + (i - 1) / 2 == 20 // This invariant ensures j reaches 13) &&
(j >= 13 // New invariant to ensure j does not drop below 13 until loop ends
          loop assigns i, j)
    */
    
            while (j >= i) {
      
      i  = i + 2;
      j  = j - 1;
      
  
    }
  
    
  
  }