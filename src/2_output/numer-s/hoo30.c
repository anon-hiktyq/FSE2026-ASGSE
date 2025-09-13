
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo30(int a) 

            /*@
            Require a % 2 == 0 && a > 0
            Ensure Results(__return)
            */
            {
    // variable declarations
   int x, r;
    //precondition
   r = 0;
   x = a / 2;

    // loop body
  
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((a@pre / 2 > 0) => (x >= 0)) &&
((a@pre / 2 > 0) => (r >= 0)) &&
((a@pre / 2 > 0) => (a == 2*x + r*(r - 1))) &&
((!(a@pre / 2 > 0)) => ((r == 0) && (x == a@pre / 2) && (a == a@pre))) &&
(a == a@pre
        loop assigns x, r)
    */
    
    while (x > r){
        x = x - r;
        r = r + 1;
    }
    // post-condition
    
}