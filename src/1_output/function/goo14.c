
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int fun14(int a) /*@

Require emp
Ensure (a == 0 && __return == 10 / (0 + 0)) || (a != 0 && __return == 10 / (5 + 5))
*/
{
    int x, y;
    int sum, res;
    if (a == 0){
        x = 0; y = 0;
    }
    else {
        x = 5; y = 5;
    }
    sum = x + y; 
    res = 10/sum; 
    return res;
}
int goo14() 
/*@

Require emp

Ensure Results(__return)
*/{
    int a = fun14(4);

    return 0;
}