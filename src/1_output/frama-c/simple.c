
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int simple(int p,int n,int r)

/*@

Require emp
Ensure Results(__return)
*/{
    int si;
    si = p*n*r/100;
    return si;
}