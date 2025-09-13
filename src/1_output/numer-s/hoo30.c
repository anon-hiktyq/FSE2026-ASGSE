
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo30(int a) 

            /*@
            Require a % 2 == 0 && a > 0
            Ensure Results(__return)
            */
            {
    // variable declarations
   int x, r;
    //precondition
   r = 0;
   x = a / 2;

    // loop body
   while (x > r){
       x = x - r;
       r = r + 1;
   }
    // post-condition
    
}