
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo027(int l,int n) 

            /*@
            Require l > 0
            Ensure Results(__return)
            */
            {
  int i, k;
 

  k = 1;
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for (k = 1; k < n; k++) {
    i = l;
   
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv emp */ /*1*/ 
 for (i = l; i < n; i++) {

    }

    
  }

}