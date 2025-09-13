
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0011(int n0, int n1) 

            /*@
            Require INT_MIN < n0 && n0 < INT_MAX && INT_MIN < n1 && n1 < INT_MAX
            Ensure Results(__return)
            */
            {
 
  int i0 = 0;
  int k = 0;
 

  while( i0 < n0 ) {
    i0++;
    k++;
  }

  int i1 = 0;
 
  while( i1 < n1 ) {
    i1++;
    k++;
  }

  int j1 = 0;
  
  
  while( j1 < n0 + n1 ) {
    
    j1++;
    k--;
  }
}