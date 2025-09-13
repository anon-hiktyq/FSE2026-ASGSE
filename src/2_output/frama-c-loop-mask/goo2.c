
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int goo2(int x, int y) 
/*@

Require emp
Ensure Results(__return)
*/{
    int r = x;
    int d = 0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((x@pre >= y@pre) => (r == x@pre - d * y@pre)) &&
((x@pre >= y@pre) => (d == quotient(x@pre, y@pre) - quotient(r, y@pre))) &&
((!(x@pre >= y@pre)) => ((d == 0)&&(r == x@pre)&&(y == y@pre)&&(x == x@pre))) &&
(y == y@pre) &&
(x == x@pre)
    */
    
    while (r >= y) {
        r = r - y;
        d = d + 1;
    }
    return d;
}