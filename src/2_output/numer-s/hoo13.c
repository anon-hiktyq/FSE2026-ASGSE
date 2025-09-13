
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo13(int x)

            /*@
            Require x == 1 || x == 2
            Ensure Results(__return)
            */
            {

    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (((x == x@pre)) || (x == 1 || x == 2)
          loop assigns x)
    */
    
            while (unknown()) {
        if(x == 1) 
            x = 2;
        else if(x == 2)
            x = 1;
    }

    //post-condition
    
}