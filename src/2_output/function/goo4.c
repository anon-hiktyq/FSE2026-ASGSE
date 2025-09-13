
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void goo4()
/*@

Require emp

Ensure emp
*/{
    int i=0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= i && i <= 30) &&
(forall (k:Z), 0 <= k && k <= i => k <= 30
      loop assigns i)
    */
    
    while (i < 30){
        ++i;
    }
    
}