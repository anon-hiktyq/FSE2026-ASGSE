
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo53(int n, int l) 

            /*@
            Require l > 0 && n > l
            Ensure Results(__return)
            */
            {
  int i,k;

  k = 1;
  for (k=1; k<n; k++){
  	i = l;
    for (i=l; i<n; i++) {
    }

    }
  
    
  

}