
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo66(int n)


            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int x=0;
  int y=0;
  int i=0;
  int m=10;
  
 
  while(i < n) {
    i++;
    x++;
    if(i%2 == 0) y++;
  }
  
  
}