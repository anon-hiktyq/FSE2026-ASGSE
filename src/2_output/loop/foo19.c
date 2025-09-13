
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo19(int y) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 1;
    
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (y >= 0 || (x == 1 && y == y@pre)) &&
(x >= 1 && x <= 11)
    */
    
    while (x <= 10) {
        y = 10 - x;
        x = x + 1;
    }

    

}