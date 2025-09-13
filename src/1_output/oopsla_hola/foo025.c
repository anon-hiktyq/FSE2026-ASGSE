
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo025() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
  while(unknown1())
  {
    
    while(unknown2())
    {
       if(x == y){
          i++;
       }else{
          j++;
       }
    }

    if(i >= j)
    {
       x++;
       y++;
    }
    else{
       y++;
    }
  }

  
}