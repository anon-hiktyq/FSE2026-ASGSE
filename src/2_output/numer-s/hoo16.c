
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo16()

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 0;
    int y = 0;
    int z = 0;

   
    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= 0) &&
(y >= 0) &&
(z % 2 == 0) &&
(x + y + z == 0
            loop assigns x, y, z)
    */
    
            while (x > 0) {
        x++;
        y++;
        z -= 2;
    }

    //post-condition
    
}