
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0013(int n, int m , int l) 

            /*@
            Require INT_MIN < n && n < INT_MAX && INT_MIN < m && m < INT_MAX && INT_MIN < l && l < INT_MAX && 3*n <= m + l
            Ensure Results(__return)
            */
            {
    int i, j, k;

    i = 0;
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for (i = 0; i < n; i++) {
        j = 2 * i;
       
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv emp */ /*1*/ 
 for (j = 2 * i; j < 3 * i; j++) {
            k = i;
            
           
  /*@ Print user assertion at number LoopEntry_2*/ 
/*@ Inv emp */ /*2*/ 
 for (k = i; k < j; k++) {
                
            }
        }
    }
}