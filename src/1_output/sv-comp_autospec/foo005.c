
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo005(int n, int x, int y) 

            /*@
            Require n > 0 && y == n
            Ensure Results(__return)
            */
            {
    x = n;
    y = 0;


    while (x > 0) {
        x++;
        y--;
    }

    
}