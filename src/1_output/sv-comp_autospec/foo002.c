
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo002(int A[2048]) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int i = 0;

  
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }

  
}