
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo92(int z1,int z2,int z3) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

    int x = 0;
    int y = 0;

    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (y == 0 // Invariant stating y is always zero) &&
(x == 0  // Invariant stating x is always zero) &&
(z3 == z3@pre // Invariant for z3's initial value) &&
(z2 == z2@pre // Invariant for z2's initial value) &&
(z1 == z1@pre // Invariant for z1's initial value
      loop assigns y // Assignments that may occur in the loop)
    */
    
    while(y >= 0) {
        y = y + x;
    }
    

}