
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