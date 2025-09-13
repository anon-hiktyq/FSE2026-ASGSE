
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo022() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= 0) &&
(y >= 0) &&
(z >= 0) &&
(x == y && y == z) &&
((k == 0 && z == 0 && y == 0 && x == 0) || (k == x + y + z)
          loop assigns x, y, z, k)
    */
    
            while(unknown())
  {
     if(k%3 == 0){
        x++;
     }
      
     y++;
     z++;
     k = x+y+z;
  }

  
 
}