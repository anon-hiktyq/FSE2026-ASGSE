
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo25(int n,int a) 

            /*@
            Require n > 0
            Ensure Results(__return)
            */
            { 
    
    int i = 0;
    int sn = 0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (0 <= i && i <= n@pre)) &&
((0 < n@pre) => (sn == i * a)) &&
((!(0 < n@pre)) => ((sn == 0)&&(i == 0)&&(a == a@pre)&&(n == n@pre))) &&
(a == a@pre) &&
(n == n@pre
          loop assigns sn, i)
    */
    
            while(i < n) {
      sn = sn + a;
      i++;
    }
  
    
  }