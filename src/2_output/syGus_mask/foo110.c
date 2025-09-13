
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo110(int n) 

            /*@
            Require n >= 1
            Ensure Results(__return)
            */
            {

    int i = 1;
    int sn = 0;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((n@pre >= 1) => ((1 <= n@pre) => (1 <= i && i <= n + 1))) &&
((n@pre >= 1) => ((1 <= n@pre) => (sn == i - 1))) &&
((n@pre >= 1) => ((!(1 <= n@pre)) => ((sn == 0) && (i == 1) && (n == n@pre)))) &&
((n@pre >= 1) => (n == n@pre)
        loop assigns i, sn)
    */
    
    while (i <= n) {
        i = i + 1;
        sn = sn + 1;
    }
    
  
  }