
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo031(int i,int j,int k,int n,int m) 

            /*@
            Require m + 1 < n
            Ensure Results(__return)
            */
            {

  i = 0;
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for (i = 0; i < n; i += 4) {
    j = i;
   
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv emp */ /*1*/ 
 for (j = i; j < m;) {
        
      if (unknown()) {
        
        j++;
        k = 0;
       
  /*@ Print user assertion at number LoopEntry_2*/ 
/*@ Inv emp */ /*2*/ 
 while (k < j) {
          k++;
        }
      } else {
        
        j += 2;
      }
    }
  }
}