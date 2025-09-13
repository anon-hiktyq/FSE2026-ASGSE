
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main20(int n)

            /*@
            Require n >= 0
            Ensure Results(__return)
            */
            {
    // variable declarations
    a,s,t;

    //precondition
    int a=0;
    int s=1;
    int t=1;

    // loop body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (a >= 0) &&
(t == 1 + 2 * a)
    */
    
            while(s <= n){
     a = a + 1;
     t = t + 2;
     s = s + t;
    }

    // post-condition
    
}