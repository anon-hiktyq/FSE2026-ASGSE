
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo1(int k)

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int i = 1;
    int j = 1;

    //pre-condition
 

    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (k <= k@pre) &&
(i >= 1) &&
(i + k <= 2
        loop assigns i, j, k)
    */
    
    while (unknown()) {
        i = i + 1;
        j = j + k;
        k = k - 1;
    }

    //post-condition
    
}