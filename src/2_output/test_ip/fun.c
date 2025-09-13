
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    typedef struct s {
    int *a;
} s;

void fun(s *p) 
/*@
With p_a_v p_a
Require *(p->a) == p_a_v && (p->a) == p_a
Ensure ((p->a == p_a) * (*p_a == p_a_v + 1))
*/
{
    *(p->a) = *(p->a)+1;
}