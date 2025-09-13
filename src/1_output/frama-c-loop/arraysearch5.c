
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int arraysearch5(int* a, int x, int n) 
/*@
With a_l
Require store_int_array(a, x, a_l) && x > 0 && x < 100
Ensure Results(__return)
*/{ 

  for (int p = 0; p < n; p++) {
    // STart
    if (x == a[p]) 
       return 1;
    // End
  }
  return 0;
}