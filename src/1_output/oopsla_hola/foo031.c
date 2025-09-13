
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
  for (i = 0; i < n; i += 4) {
    j = i;
    for (j = i; j < m;) {
        
      if (unknown()) {
        
        j++;
        k = 0;
        while (k < j) {
          k++;
        }
      } else {
        
        j += 2;
      }
    }
  }
}