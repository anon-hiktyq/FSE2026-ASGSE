
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo2(int y,int z)


            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 0;   

    
    
 
/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= x && x <= 500) &&
(z == z@pre) &&
((x == 0 && y == y@pre) || (z >= y))
    */
    
    while(x < 500) {
        x += 1;
        if(z <= y) {
            y = z;
        }
    }


   
    
}