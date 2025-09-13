
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int func26(int num) /*@

Require emp
Ensure (num <= 0 && __return == 0)
*/
{
    int i = 0;
    int sum = 0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while(num>0) {
        i = num%10;
        sum += i;
        num /= 10;
    }
    return sum;
}
void goo26() 
/*@

Require emp

Ensure emp
*/{
    int t = func26(123);
    
}