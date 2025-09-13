
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int arraymax22(int* a, int n) 
/*@
With a_l
Require store_int_array(a, n, a_l) && n > 0 && n < 100
Ensure Results(__return)
*/{
  int i = 1;
  int max = a[0];

  while (i < n) {
    // Beginning of loop
    if (max < a[i])
    max = a[i];
    i = i + 1;
    // End of loop: Loop invariant comes here
  }
  return max;
}