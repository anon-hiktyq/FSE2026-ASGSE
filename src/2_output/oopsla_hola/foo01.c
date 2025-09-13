
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo01() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
 int x = 1;
 int y = 1;


  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (((y == 1)&&(x == 1)) || (x == y)) &&
(((y == 1)&&(x == 1)) || (x >= 1)) &&
(((y == 1)&&(x == 1)) || (y >= 1)
      loop assigns x, y)
    */
    
    while(unknown()) {
        int t1 = x;
        int t2 = y;
        x = t1 + t2;
        y = t1 + t2;
    }
 
}