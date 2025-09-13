#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */


int main(int a[10])
/*@ With l a_0
    Require store_int_array(a, 10, l) && l[1] == a_0
    Ensure  __return == sum(l) && store_int_array(a, 10, l)
*/
{
    a[1] = 0;

    return 0;
}