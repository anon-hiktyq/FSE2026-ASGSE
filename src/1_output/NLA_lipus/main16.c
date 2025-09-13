
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main16(int k)

            /*@
            Require k >= 0 && k <= 30
            Ensure Results(__return)
            */
            {
   
    int y=0;
    int x=0;
    int c=0;


    // loop body
    while(c < k){
     c = c + 1;
     y = y + 1;
     x = y * y + x;
    }
    
}