
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo58() 

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
    (0 <= x) &&
(0 <= y) &&
(w == 0 || w == 1) &&
(z == 0 || z == 1
    loop assigns x, y, w, z)
    */
    
  while(unknown()){
    if(w) {
      x++;
      w = !w;
    }
    
    if(!z) {
      y++; 
      z = !z;
    }
  }

  
  
}