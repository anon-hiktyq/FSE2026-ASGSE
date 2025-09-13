
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int func8(int c) /*@

Require emp
Ensure Results(__return)
*/
{
    int x = c;
    int y = 0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((c@pre > 0) => (y + x == c@pre)) &&
((c@pre > 0) => (x >= 0)) &&
((!(c@pre > 0)) => ((y == 0)&&(x == c@pre)&&(c == c@pre))) &&
(c == c@pre
      loop assigns x, y)
    */
    
    while(x > 0) {
        x = x - 1;
        y = y + 1;
    }
    return y;
}
void goo8() 
/*@

Require emp

Ensure emp
*/{
    int t = func8(5);
    
}