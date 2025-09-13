
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main3(int x,int y)

            /*@
            Require x > 0 && y > 0
            Ensure Results(__return)
            */
            {
 
    int q=0;
    int r=0;
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= q * y + r) &&
(q >= 0) &&
(r >= 0 && r < y) &&
(y == y@pre) &&
(x == x@pre
      loop assigns q, r)
    */
    
    while (x > y * q + r) {
        if (r == y - 1) {
            r = 0;
            q += 1;
        } else {
            r += 1;
        }
    }
    
  }