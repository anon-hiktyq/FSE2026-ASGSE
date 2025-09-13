
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0017(int tmp, int A[2048], int B[2048]) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int i = 0;
  
  for (i = 0; i < 2048; i++) {
    tmp = A[i];
    B[i] = tmp;
  }

  
}