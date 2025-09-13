
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo8()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    

    //pre-condition
    int x = 0;

    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x % 4 == 0) &&
(x >= 0 
            loop assigns x)
    */
    
            while(unknown()){
        x = x + 4;
    }

    //post-condition
    
    
}