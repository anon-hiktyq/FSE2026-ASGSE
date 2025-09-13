
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

  
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  A_l,    
    store_int_array(A, 2048, A_l) &&
    (0 <= i && i <= 1024) &&
(forall (j:Z), 0 <= j && j < i => A_l[j] == j) &&
(A == A@pre
            loop assigns A_l[0..1023], i)
    */
    
            for (i = 0; i < 1024; i++) {
    A[i] = i;
  }

  
}