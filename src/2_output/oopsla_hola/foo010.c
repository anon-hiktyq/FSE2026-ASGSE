
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo010() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {


  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (z <= 1) &&
(w == 1 || w == 0) &&
(0 <= x) &&
(0 <= y
    loop assigns x
    loop assigns y
    loop assigns z
    loop assigns w)
    */
    
  while(unknown()){
    if(w) {
      x++;
      w = !w;
    }

    if(!z) {
      y++; 
      z=!z;
    }
  }

  
  
}