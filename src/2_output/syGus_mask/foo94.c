
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo94(int n,int k) 

            /*@
            Require n >= 0 && k >= 0
            Ensure Results(__return)
            */
            {
  
    int i = 0;
    int j = 0;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((n@pre >= 0 && k@pre >= 0) => ((0 <= n@pre) => (0 <= i && i <= n + 1))) &&
((n@pre >= 0 && k@pre >= 0) => ((0 <= n@pre) => (j == (i * (i + 1)) / 2))) &&
((n@pre >= 0 && k@pre >= 0) => ((!(0 <= n@pre)) => ((j == 0)&&(i == 0)&&(k == k@pre)&&(n == n@pre)))) &&
((n@pre >= 0 && k@pre >= 0) => (k == k@pre)) &&
((n@pre >= 0 && k@pre >= 0) => (n == n@pre)
              loop assigns i, j)
    */
    
            while (i <= n) {
      
       i  = i + 1;
       j  = j + i;
      
  
    }
  
  }