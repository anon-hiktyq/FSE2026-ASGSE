
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int incr_a_by_b(int* a, int * b)
/*@
With a_v b_v
Require *(a) == a_v && *(b) == b_v
Ensure Results(__return)
*/{
    *a += *b;
    return *a;
}