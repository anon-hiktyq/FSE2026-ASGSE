
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo21(int X,int Y) 

            /*@
            Require X > 0 && Y > 0 && X >= Y
            Ensure Results(__return)
            */
            {
    
    int v, x, y;

    v = 2 * Y - X;
    y = 0;
    x = 0;


    
    while (x <= X) {
        if (v < 0) {
            v = v + 2 * Y;
        } else {
            v = v + 2 * (Y - X);
            y++;
        }
        x++;

    }

    
    
}