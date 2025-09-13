
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo23() 


            /*@
            Require a > 0 && b > 0
            Ensure Results(__return)
            */
            {
    
    int a, b;
    int product = 0; 
    int i = 0;


    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while (i < b) {
        product = product + a;  
        i = i + 1;
    }

    
    
    
}