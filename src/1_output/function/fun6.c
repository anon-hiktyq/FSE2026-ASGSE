
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int fun6(int x) 
/*@

Require emp
Ensure Results(__return)
*/{
    int a = x;
    int y = 0;

    while(a != 0) {
        y = y + 1;
        a = a - 1;
    }
    return y;
}