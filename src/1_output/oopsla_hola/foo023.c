
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo023(int n) 

            /*@
            Require n >= 0
            Ensure Results(__return)
            */
            {
  int i, sum = 0;
 
  for (i = 0; i < n; ++i){
    sum = sum + i;
  }

  
}