
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo041(int n, int flag) 

            /*@
            Require n > 0
            Ensure Results(__return)
            */
            {
  int k = 1;
  if (flag) {
    k = unknown1();
  }
  int i = 0, j = 0;
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((i <= n) => (j == i * (i + 1) / 2)
        loop assigns i, j)
    */
    
            while (i <= n) {
    i++;
    j += i;
  }
  int z = k + i + j;
  
}