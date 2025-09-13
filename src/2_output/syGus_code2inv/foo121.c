
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo121() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
 
    int i = 1;
    int sn = 0;
    
     
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (i == 1 + sn) &&
(sn >= 0) &&
(sn <= 8
      loop assigns i, sn)
    */
    
    while (i <= 8) {
  
      i  = (i + 1);
      sn  = (sn + 1);
      
    }
  
    
  
  }