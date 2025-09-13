
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo82(int x, int y,int z1,int z2,int z3) 

            /*@
            Require x >= y && y >= 0
            Ensure Results(__return)
            */
            {

    int i = 0;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((x@pre >= y@pre && y@pre >= 0) => (0 <= i && i <= y)) &&
((x@pre >= y@pre && y@pre >= 0) => (z3 == z3@pre)) &&
((x@pre >= y@pre && y@pre >= 0) => (z2 == z2@pre)) &&
((x@pre >= y@pre && y@pre >= 0) => (z1 == z1@pre)) &&
((x@pre >= y@pre && y@pre >= 0) => (y == y@pre)) &&
((x@pre >= y@pre && y@pre >= 0) => (x == x@pre)
      loop assigns i)
    */
    
    while (unknown()) {
        if (i < y) {
            i = i + 1;
        }
    }


}