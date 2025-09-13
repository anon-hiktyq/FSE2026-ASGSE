
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main2(int x,int y)

            /*@
            Require x > 0 && y > 0
            Ensure Results(__return)
            */
            {
 
  int q=0;
  int r=0;
  
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= q) &&
(0 <= r && r < y) &&
((x == y * q + r) || (x > y * q + r)) &&
(y == y@pre) &&
(x == x@pre)
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