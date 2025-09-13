
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo64() 

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
    (x == y) &&
(x >= 0) &&
(n == 0
    loop assigns x, y
    loop variant 0)
    */
    
  while(unknown()) {
      x++;
      y++;
  }
 
 
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv
    (x >= n) &&
(x == y
    loop assigns x, y
    loop variant x - n)
    */
    
  while(x != n) {
      x--;
      y--;
  }
  
}