
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo004() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int i, j;
    i = 1;
    j = 10;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= j && j <= 10) &&
(i == 1 + 2 * (10 - j)) &&
(j == 10 - (i - 1) / 2 // Existing invariant) &&
(j == 6 + (10 - i) / 2 // New invariant to ensure j will be 6 at termination
      loop assigns i, j)
    */
    
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
    
    
    return 0;
}