
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo011() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int j = 0;
  int i = 0;
  int x = 100;
   
 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (j == 2 * i) &&
(0 <= i && i <= x) &&
(x == 100
              loop assigns j, i)
    */
    
            for (i = 0; i < x ; i++){
    j = j + 2;
  }

  
}