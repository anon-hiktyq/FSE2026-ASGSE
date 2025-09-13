
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo22(int y) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 1;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (((x == 1 && y == y@pre) || (y == 100 - (x - 1)))) &&
(x >= 1 && x <= 101
      loop assigns x, y
      loop variant 101 - x)
    */
    
    while (x <= 100) {
        y = 100 - x;
        x = x + 1;
    }

    

}