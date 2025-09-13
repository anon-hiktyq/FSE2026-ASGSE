
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo026() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int w = 1, z = 0, x = 0, y = 0;
 
  while (unknown1()) {
   
    while (unknown2()) {
      if (w % 2 == 1)
        x++;
      if (z % 2 == 0)
        y++;
    }
   
    while (unknown3()) {
      z = x + y;
      w = z + 1;
    }
  }
  
}