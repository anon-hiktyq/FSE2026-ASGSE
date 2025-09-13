
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo132(int j,int c,int t) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    int i = 0;



 
/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (i >= 0) &&
(((i == 0) && (t == t@pre) && (c == c@pre) && (j == j@pre)) || (t == c - 48)) &&
(((i == 0) && (t == t@pre) && (c == c@pre) && (j == j@pre)) || (i == j + t)) &&
(c == c@pre
      loop assigns i, j, t)
    */
    
    while (unknown()) {
        if (c > 48) {
            if (c < 57) {
                j = i + i;
                t = c - 48;
                i = j + t;
            }
        }
    } 
 


}