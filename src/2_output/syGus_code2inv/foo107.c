
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo107(int m,int j,int a) 

            /*@
            Require a <= m
            Ensure Results(__return)
            */
            {

    int k = 0;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= k && k <= 1) &&
(a@pre <= m@pre => (m >= a)) &&
((k == 0) => (m == m@pre || m == a)) &&
((k == 1) => (m >= a)) &&
(a@pre <= m@pre => (a == a@pre)) &&
(a@pre <= m@pre => (j == j@pre)
      loop assigns m, k)
    */
    
    while ( k < 1) {

        if(m < a) {
            m = a;
        }
        
        k = k + 1;
    }

  

}