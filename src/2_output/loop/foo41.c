
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo41(int n) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  
    int x = 0;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (x >= 0 && x <= n)) &&
((!(0 < n@pre)) => ((x == 0) && (n == n@pre))) &&
(n == n@pre
      loop assigns x
      loop variant n - x)
    */
    
    while (x < n) {
        x = x + 1;
    }
    
    
  }