
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo3() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    //pre-condition
    int s = 0;

    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (s == 0
        loop assigns s)
    */
    
    while(unknown()){
        if (s != 0){
            s = s + 1;
        }
    }

    //post-condition
    

}