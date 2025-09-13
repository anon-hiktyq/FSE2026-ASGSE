
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