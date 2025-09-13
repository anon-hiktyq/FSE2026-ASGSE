
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int test(int A,int x) 
/*@

Require emp
Ensure (__return >= 0 && __return <= A - 1)
*/
{

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x <= A-1) &&
(A == A@pre)
    */
    
        while (x < 0)  {
            x = x + A;
        }   
    
    return x;
}