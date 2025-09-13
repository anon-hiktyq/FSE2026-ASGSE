
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo11(int y)

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 0;

    //pre-condition
    
    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((y == y@pre) // y remains constant) &&
((y % 2 == 0 => (x % 2 == 0)) // x is even if y is even
      loop assigns x)
    */
    
    while (x < 99) {
        if (y % 2 == 0) 
            x += 10;
        else 
            x -= 5;
    }

    //post-condition
    
}