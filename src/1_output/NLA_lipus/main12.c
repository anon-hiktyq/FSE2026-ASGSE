
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main12(int A,int B)

            /*@
            Require A >= 0 && B >= 1
            Ensure Results(__return)
            */
            {
    
   
    int q = 0;
    int r = 0;
    int t = A;
   
    
    while(t != 0) {
     if (r + 1 == B) {
          q = q + 1;
          r = 0;
          t = t - 1;
     }
     else {
          r = r + 1;
          t = t - 1;
     }
    }
    
}