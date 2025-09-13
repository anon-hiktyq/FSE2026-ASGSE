
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo038(int n) 

            /*@
            Require n > 0
            Ensure Results(__return)
            */
            {
  int x=0;
  int y=0;
  int i=0;
  
 
  while(i<n) {
    i++;
    x++;
    if(i%2 == 0) y++;
  }
  
 
}