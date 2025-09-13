
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo26(int a) 

            /*@
            Require a % 2 == 0 && a > 0
            Ensure Results(__return)
            */
            {
    // variable declarations
    int x = a / 2;
    int r = 0;

    // loop body
  
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (r >= 0) &&
(x >= 0
          loop assigns x, r)
    */
    
            while (x > r){
       x = x - r;
       r = r + 1;
   }
    // post-condition
    
}