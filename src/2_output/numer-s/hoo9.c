
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo9()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    //pre-condition
    int x = 1;

    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x % 2 == 1) &&
(x >= 1
            loop assigns x)
    */
    
            while(unknown()){
        x = x + 2;
    }

    //post-condition
    
    
}