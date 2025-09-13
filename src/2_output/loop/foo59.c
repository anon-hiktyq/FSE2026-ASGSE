
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo59(int flag, int a) 

            /*@
            Require flag > 0
            Ensure Results(__return)
            */
            {
   int b = 0;
   int j = 0;
 
  
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= b && b <= 100) &&
(flag => j == b) &&
(a == a@pre) &&
(flag == flag@pre
      loop assigns j, b
      loop variant 100 - b)
    */
    
   for (b = 0; b < 100; ++b) {
      if (flag)
         j = j + 1;
   }

   
}