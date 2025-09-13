
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo06() 
/*@

Require emp

Ensure emp
*/{
  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  
  while(unknown1()) {
	  
    while(unknown2()){
      if(w%2 == 1) x++;
      if(z%2 == 0) y++;
    }
    z = x + y;
    w = z + 1;
  }

   
}