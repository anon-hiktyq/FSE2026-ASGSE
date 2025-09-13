
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0010(int i, int j) 

            /*@
            Require 0 <= i && i < 1000000 && j >= 0
            Ensure Results(__return)
            */
            {

    int x = i;
    int y = j;
    int z = 0;
  
    while (x != 0) {
        x--;
        y -= 2;
        z++;
    }

    if (i == j) {
        
    }
    
}