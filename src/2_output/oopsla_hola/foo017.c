
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo017(int n) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
 int k=1;
 int i=1;
 int j=0;
 

  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while(i < n) {
  j = 0;
 
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv emp */ /*1*/ 
 while(j < i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 ;
 
}