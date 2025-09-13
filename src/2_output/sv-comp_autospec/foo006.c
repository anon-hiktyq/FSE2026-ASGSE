
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo006(int k) 

            /*@
            Require 0 <= k && k <= 1
            Ensure Results(__return)
            */
            {
    int i, j;
    i = 1;
    j = 1;


   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (k == k@pre - (i - 1)) &&
(i >= 1) &&
(j == 1 + (i - 1) * k@pre - (i - 1) * (i - 2) / 2
        loop assigns i, j, k)
    */
    
    while (i < 1000000) {
        i = i + 1;
        j = j + k;
        k = k - 1;
        /*@ assert 1 <= i + k && i + k <= 2 && i >= 1;*/
    }
}