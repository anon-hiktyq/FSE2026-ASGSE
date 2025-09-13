
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int fun1(int a[10],int n)
/*@
With a_l
Require store_int_array(a,10, a_l)
Ensure (__return == replace_Znth(2, 3, replace_Znth(1, 2, replace_Znth(0, 1, a_l)))[1] && store_int_array(a, 10, replace_Znth(2, 3, replace_Znth(1, 2, replace_Znth(0, 1, a_l)))))
*/
{
    a[0] = 1;
    a[1] = 2;
    a[2] = 3;
    return a[1];
}