
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0014(int n) 

            /*@
            Require 0 <= n && n < 1000
            Ensure Results(__return)
            */
            {

    int i=0;
    int sn=0;
    
   
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 <= n@pre) => (0 <= i && i <= n + 1)) &&
((0 <= n@pre) => (sn == 2 * (i - 1))) &&
((!(0 <= n@pre)) => ((sn == 0)&&(i == 0)&&(n == n@pre))) &&
(n == n@pre
            loop assigns i, sn)
    */
    
            for (i = 1; i <= n; i++) {
        sn = sn + (2);
    }
    
    
}