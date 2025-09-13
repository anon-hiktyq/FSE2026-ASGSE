
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo71(int y) 

            /*@
            Require y >= 0 && y <= 127
            Ensure Results(__return)
            */
            {
    int c = 0;
    int z = 36 * y;
    
  
  
  
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((y@pre >= 0 && y@pre <= 127) => (0 <= c && c <= 36)) &&
((y@pre >= 0 && y@pre <= 127) => (z == 36 * y@pre + c)) &&
((y@pre >= 0 && y@pre <= 127) => (y == y@pre)
        loop assigns c, z)
    */
    
    while (unknown()) {
        if (c < 36) {
            z = z + 1;
            c = c + 1;
        }
    }

  
  
  
  }