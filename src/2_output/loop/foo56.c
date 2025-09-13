
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void  foo56(int k) 

            /*@
            Require 0 <= k && k <= 1
            Ensure Results(__return)
            */
            {
    int i,j;
    i = 1;
    j = 1;
   

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (i >= 1 && i <= 1000000) &&
(i + k == k@pre + 1
        loop assigns i, j, k
        loop variant 1000000 - i)
    */
    
    while (i < 1000000) {
        i = i + 1;
        j = j + k;
        k = k - 1;
        /*@ assert 1 <= i + k && i + k <= 2 && i >= 1;*/
    }
    
}