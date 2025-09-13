
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo36(int n) 

            /*@
            Require n > 0
            Ensure Results(__return)
            */
            {
    
    int sum = 0;   
    int i = 1;     

    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((1 <= n@pre) => (sum == (i - 1) * i / 2) ) &&
((1 <= n@pre) => (1 <= i && i <= n@pre + 1) ) &&
((!(1 <= n@pre)) => ((i == 1)&&(sum == 0)&&(n == n@pre))) &&
(n == n@pre
          loop assigns sum, i)
    */
    
            while (i <= n) {
        sum = sum + i;  
        i = i + 1;      
    }

    
    
    
}