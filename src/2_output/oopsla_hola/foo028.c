
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo028() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int x = 0;
  int y = 0;
  int n = 0;
 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= 0) &&
(y == x) &&
(n == 0
    loop assigns x, y)
    */
    
  while(unknown()) {
      x++;
      y++;
  }
 
 
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv
    (y >= x - n) &&
(x >= y) &&
(n == 0
    loop assigns x, y)
    */
    
  while(x != n) {
      x--;
      y--;
  }
  
}