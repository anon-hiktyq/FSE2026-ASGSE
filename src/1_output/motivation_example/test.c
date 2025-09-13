
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int test(int A,int x) 
/*@

Require emp
Ensure Results(__return)
*/{

    while (x < 0)  {
        x = x + A;
    }   
    
    return x;
}