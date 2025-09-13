
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo7(int a)

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
    (x % 2 == 0
            loop variant 1 // Indicates that the loop has a variant)
    */
    
            while(unknown()){
        x = x + 2;
    }

    //post-condition
    
    
}