
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo34(int n,int v1,int v2,int v3) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    int x = n;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (n >= 0 => (x >= 0)) &&
(x == n@pre - (n - n@pre + (n@pre - x))
      loop assigns x)
    */
    
    while (x > 0) {
        x = x - 1;
    }
  
   
  }