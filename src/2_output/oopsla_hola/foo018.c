
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo018(int flag, int a) 

            /*@
            Require flag > 0
            Ensure Results(__return)
            */
            {
   int b = 0;
   int j = 0;
 
  
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (flag > 0 => (j == b)) &&
(0 <= b && b <= 100) &&
(a == a@pre) &&
(flag == flag@pre
              loop assigns j, b)
    */
    
            for (b = 0; b < 100 ; ++b){
      if (flag)
         j = j + 1;
   }

   
}