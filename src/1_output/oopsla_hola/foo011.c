
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo011() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int j = 0;
  int i = 0;
  int x = 100;
   
 
  for (i = 0; i < x ; i++){
    j = j + 2;
  }

  
}