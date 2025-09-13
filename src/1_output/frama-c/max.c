
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int max ( int x, int y ) 
/*@

Require emp
Ensure Results(__return)
*/{
    if ( x >=y ) 
        return x ;
    return y ;
}