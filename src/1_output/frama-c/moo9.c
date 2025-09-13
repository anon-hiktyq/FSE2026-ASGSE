
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int diff (int x, int y) /*@

Require emp
Ensure (__return == x - y)
*/
{
    return x-y;
}
void moo9() 
/*@

Require emp

Ensure emp
*/{
    int t = diff(10, 5);
    
}