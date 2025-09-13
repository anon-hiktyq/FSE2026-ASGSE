
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo75(int y,int x1,int x2,int x3) 

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
((y@pre >= 0 && y@pre <= 127) => (z == 36 * y + c)) &&
((y@pre >= 0 && y@pre <= 127) => (x3 == x3@pre)) &&
((y@pre >= 0 && y@pre <= 127) => (x2 == x2@pre)) &&
((y@pre >= 0 && y@pre <= 127) => (x1 == x1@pre)) &&
((y@pre >= 0 && y@pre <= 127) => (y == y@pre)
    loop assigns z, c)
    */
    
  while (unknown()) {
    if (c < 36) {
      z = z + 1;
      c = c + 1;
    }
  }
      
  
}