
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo043(int x, int y) 

            /*@
            Require x != y
            Ensure Results(__return)
            */
            {
  int i=0;
  int t=y;
   
  

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (y >= t // Ensures y is at least t) &&
(t == y@pre) &&
(i >= 0 // Adjusted to reflect non-negativity) &&
(x == x@pre
              loop assigns y, i)
    */
    
            while (unknown()){
    if (x > 0)   
      y = y + x;
      i = i + 1;
  }
   
  
 
}