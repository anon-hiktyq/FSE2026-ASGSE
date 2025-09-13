
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    


int fun17(int n) /*@

Require emp
Ensure (7 > n && __return == 1)
*/
{
    int i = 7;
    int x = 1;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while(i <= n) {
        x += 1;
        i += 3;
    }
    return x;
}
int main17() 
/*@

Require emp

Ensure Results(__return)
*/{
    int a = fun17(10);
    
}