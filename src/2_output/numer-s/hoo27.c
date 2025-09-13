
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo27(int x,int y) 

            /*@
            Require x >= 0 && y >= 1
            Ensure Results(__return)
            */
            {
    int q = 0;
    int a = 0;
    int b = x;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((x@pre != 0) => (q * y + a + b == x@pre)) &&
((x@pre != 0) => (0 <= a && a < y)) &&
((x@pre != 0) => (b >= 0)) &&
((!(x@pre != 0)) => ((b == x@pre)&&(a == 0)&&(q == 0)&&(y == y@pre)&&(x == x@pre))) &&
(y == y@pre) &&
(x == x@pre
          loop assigns q, a, b)
    */
    
            while(b != 0) {
        if (a + 1 == y) {
            q = q + 1;
            a = 0;
            b = b - 1;
        }
        else {
            a = a + 1;
            b = b - 1;
        }
    }

    
}