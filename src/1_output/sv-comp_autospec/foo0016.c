
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0016(int n) 

            /*@
            Require n > 0
            Ensure Results(__return)
            */
            {
 
  int i = 0;
  int k = 0;
  
  
  while( i < n ) {
	  i++;
	  k++;
  }

  int j = 0;
 
  while( j < n ) {
    
    j++;
    k--;
  }
}