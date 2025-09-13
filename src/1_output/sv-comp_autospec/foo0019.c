
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0019(int n) 

            /*@
            Require n <= INT_MAX
            Ensure Results(__return)
            */
            {
  int i,k;
  k = n;
  i = 0;

  
  while( i < n ) {
    k--;
    i = i + 2;
  }

  int j = 0;

  
  while( j < n/2 ) {
    
    k--;
    j++;
  }
}