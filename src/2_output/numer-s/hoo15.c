
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo15()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 0;
    int y = 0;

  

    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x == 4 * y) &&
(y >= 0 // y is non-negative since it starts at 0 and only increments
      loop assigns x, y // x and y are the variables being modified in the loop)
    */
    
    while (unknown()) {
        x += 4;
        y++;
    }

    //post-condition
    
}