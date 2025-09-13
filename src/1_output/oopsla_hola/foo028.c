
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo028() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int x = 0;
  int y = 0;
  int n = 0;
 
  while(unknown()) {
      x++;
      y++;
  }
 
  while(x!=n) {
      x--;
      y--;
  }
  
}