
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int fun1(int x, int y , int *r) 
/*@
With r_v
Require *(r) == r_v
Ensure Results(__return)
*/{
    *r = x;
    int d = 0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((r_v >= y@pre) => (*r == r_v - d * y@pre)) &&
((r_v >= y@pre) => (d == (r_v - *r) / y@pre)) &&
((!(r_v >= y@pre)) => ((d == 0)&&(r == r@pre)&&(y == y@pre)&&(x == x@pre)&&(r_v == x@pre))) &&
(y == y@pre) &&
(x == x@pre) &&
(r_v == x@pre
    loop assigns *r, d
    loop variant *r)
    */
    
    while (*r >= y) {
        *r = *r - y;
        d = d + 1;
    }
    return d;
}