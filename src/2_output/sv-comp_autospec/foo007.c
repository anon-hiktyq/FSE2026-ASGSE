
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo007(int n) 

            /*@
            Require 0 < n
            Ensure Results(__return)
            */
            {
    int k = 0;
    int i = 0;


   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (k == i)) &&
((0 < n@pre) => (0 <= i && i <= n)) &&
(!(0 < n@pre) => ((i == 0)&&(k == 0)&&(n == n@pre))) &&
(n == n@pre
        loop assigns i, k)
    */
    
    while (i < n) {
        i++;
        k++;
    }
    int j = n;


   
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv emp */ /*1*/ 
 while (j > 0) {
        j--;
        k--;
        
    }


}