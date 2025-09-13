
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
  
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  A_l B_l,    
    store_int_array(A, 2048, A_l) && store_int_array(B, 2048, B_l) &&
    (0 <= i && i <= 2048) &&
(B == B@pre) &&
(A == A@pre) &&
(forall (j:Z), i <= j && j < 2048 => B_l[j] == B@pre_l[j]  // B remains unchanged for unprocessed indices
              loop assigns i, B_l[0..2047], tmp)
    */
    
            for (i = 0; i < 2048; i++) {
    tmp = A[i];
    B[i] = tmp;
  }

  
}