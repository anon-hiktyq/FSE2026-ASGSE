
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo77(int x, int y) 

            /*@
            Require x >= y && y >= 0
            Ensure Results(__return)
            */
            {

    int i = 0;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((x@pre >= y@pre && y@pre >= 0) => (0 <= i && i <= y)) &&
((x@pre >= y@pre && y@pre >= 0) => (y == y@pre)) &&
((x@pre >= y@pre && y@pre >= 0) => (x == x@pre)
        loop assigns i)
    */
    
    while (unknown()) {
        if (i < y) {
            i = (i + 1);
        }
    }
    
  

}