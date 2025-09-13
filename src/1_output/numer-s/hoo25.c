
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

    while(i < n) {
      sn = sn + a;
      i++;
    }
  
    
  }