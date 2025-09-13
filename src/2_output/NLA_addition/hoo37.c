
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo37(int a, int b) 

            /*@
            Require a >= 0 && b >= 0
            Ensure Results(__return)
            */
            {
    
    int product = 0;  
    int i = 0;        

    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < b@pre) => (product == a * i) ) &&
((0 < b@pre) => (0 <= i && i <= b) ) &&
((!(0 < b@pre)) => ((i == 0)&&(product == 0)&&(b == b@pre)&&(a == a@pre))) &&
(b == b@pre) &&
(a == a@pre
          loop assigns product, i)
    */
    
            while (i < b) {
        product = product + a;  
        i = i + 1;
    }

    
    
}