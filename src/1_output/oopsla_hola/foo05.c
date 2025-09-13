
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo05(int flag) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

	int x = 0;
	int y = 0;
	int j = 0;
	int i = 0;

   
	while(unknown())
	{
	  x++;
	  y++;
	  i += x;
	  j += y;
	  if (flag){
	  	j+=1;
      }
	} 
	
	
}