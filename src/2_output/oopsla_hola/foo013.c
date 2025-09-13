
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo013(int flag) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
   int j = 2; 
   int k = 0;

   
  
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (j >= 2 + 2 * k) &&
(k >= 0) &&
(flag == flag@pre
   loop assigns j, k)
    */
    
   while(unknown()){ 
     if (flag)
       j = j + 4;
     else {
       j = j + 2;
       k = k + 1;
     }
   }
   
}