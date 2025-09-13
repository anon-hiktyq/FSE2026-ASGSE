
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo009(int i, int j) 

            /*@
            Require i >= 0 && j >= 0
            Ensure Results(__return)
            */
            {

    int x = i;
    int y = j;
    

    while (x != 0) {
        x--;
        y--;
    }

    if (i == j) {
        
    }
    

}