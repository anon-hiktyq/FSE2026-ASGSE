
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo030() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

  int i, c;
  i = 0;
  c = 0;
 
  while (i < 1000) {
    c = c + i;
    i = i + 1;
  }

  
}