
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int max_ptr(int *a, int *b)
/*@
With a_v b_v
Require *(a) == a_v && *(b) == b_v
Ensure Results(__return)
*/{
    return (*a < *b) ? *b : *a ;
}