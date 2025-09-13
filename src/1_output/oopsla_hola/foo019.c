
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo019(int n, int m) 

            /*@
            Require n >= 0 && m >= 0 && m < n
            Ensure Results(__return)
            */
            {
 
  int x = 0; 
  int y = m;
 
  while(x < n) {
    x++;
    if(x > m) y++;
  }
  
}