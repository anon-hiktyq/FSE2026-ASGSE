
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo13(int n,int z1,int z2,int z3)


            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    int x = 1;
    int m = 1;

    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((m >= 1) && (m <= x)) &&
((n > 1) => (m < n)) &&
((z1 == z1@pre) && (z2 == z2@pre) && (z3 == z3@pre) && (n == n@pre)
      loop assigns x, m
      loop variant n - x)
    */
    
    while (x < n) {

        if (unknown()) {
            m = x;
        }
        
        x = x + 1;
    }

    

}