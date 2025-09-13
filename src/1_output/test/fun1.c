
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int fun1(int a[10],int n)
/*@
With a_l
Require store_int_array(a,10, a_l)
Ensure Results(__return)
*/{
    a[0] = 1;
    a[1] = 2;
    a[2] = 3;
    return a[1];
}