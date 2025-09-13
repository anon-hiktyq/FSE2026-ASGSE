
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo18(int n) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 1;
    int m = 1;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (n >= 1 => (1 <= x && x <= n) // x is within valid bounds when n >= 1) &&
((1 < n) => (m >= 1) // Ensure m is at least 1 if n > 1
      loop assigns x, m // x and m are modified by the loop)
    */
    
    while (x < n) {
        
        if (unknown()) {
            m = x;
        }
        
        x = x + 1;
    }
 
    

}