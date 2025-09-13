
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int foo90(int x,int v1,int v2,int v3) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    int lock = 1;
    int y = x + 1;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((x@pre != x@pre + 1) => (((y == x@pre + 1)&&(lock == 1)&&(v3 == v3@pre)&&(v2 == v2@pre)&&(v1 == v1@pre)&&(x == x@pre)) || (x <= y))) &&
((x@pre != x@pre + 1) => (((y == x@pre + 1)&&(lock == 1)&&(v3 == v3@pre)&&(v2 == v2@pre)&&(v1 == v1@pre)&&(x == x@pre)) || ((lock == 0) || (lock == 1)))) &&
((x@pre != x@pre + 1) => ((y == x + 1) || (y == x))) &&
(!(x@pre != x@pre + 1) => ((y == x@pre + 1)&&(lock == 1)&&(v3 == v3@pre)&&(v2 == v2@pre)&&(v1 == v1@pre)&&(x == x@pre))) &&
(v3 == v3@pre) &&
(v2 == v2@pre) &&
(v1 == v1@pre
      loop assigns x, y, lock)
    */
    
    while (x != y) {
        if (unknown()) {
            lock = 1;
            x = y;
        } else {
            lock = 0;
            x = y;
            y = y + 1;
        }
    }
  }