
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo0018(int flag) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    unsigned int i, j, a, b;
    a = 0;
    b = 0;
    j = 1;
    if (flag) {
        i = 0;
    } else {
        i = 1;
    }

    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (a >= 0) &&
(flag == flag@pre)
    */
    
            while (unknown1()) {
        a++;
        b += (j - i);
        i += 2;
        if (i % 2 == 0) {
            j += 2;
        } else {
            j++;
        }
    }
    if (flag) {
        
    }

}