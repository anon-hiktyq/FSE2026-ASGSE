
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo22(int a) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            { 
    
    //pre-condition
    int sn = 0;
    int x = 0;
  
    //loop-body
    while(unknown()) {
      if (x<10) {
          sn = sn + a;
          x++;
      }
    }
  
    //post-condition
    
  }