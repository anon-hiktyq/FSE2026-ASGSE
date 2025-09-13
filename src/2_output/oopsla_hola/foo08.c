
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo08() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
 int x = 0, y = 0;


  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= 0) &&
(y >= 0) &&
((x < 4) => (y >= 100 * x)) &&
((x >= 4) => (y >= 400 + (x - 4)) // Strengthened invariant) &&
((x < 0) => (y <= 0)
          loop assigns x, y)
    */
    
            while(unknown1()) {
   if(unknown2()) { 
      x++; 
      y += 100; 
   }
   else if (unknown3()){ 
      if (x >= 4) { 
          x++; 
          y++; 
      } 
      if (x < 0) {
          y--;
      }
   }
  
 }
 
}