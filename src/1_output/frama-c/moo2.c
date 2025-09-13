
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int add(int x, int y) /*@

Require emp
Ensure (__return == x + y)
*/
{
    return x+y;
}
void moo2() 
/*@

Require emp

Ensure emp
*/{
    int a = add(1, 43);
    
    int b = add(997, 997);
}