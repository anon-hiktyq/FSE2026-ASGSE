
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo0012(int n, int l) 

            /*@
            Require l > 0 && l < INT_MAX && n < INT_MAX
            Ensure Results(__return)
            */
            {
  int k = 1;

  
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for (; k < n; k++){

    int i= l;
    
   
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv emp */ /*1*/ 
 for (; i < n; i++){
      
    }
    if(unknown1()) {
      l = l + 1;
    }
  }
}