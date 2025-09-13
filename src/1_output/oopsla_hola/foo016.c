
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo016(int i, int j) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  
  int x = i;
  int y = j;
 
 
  while(x != 0) {
	  x--;
	  y--;
  }

  
}