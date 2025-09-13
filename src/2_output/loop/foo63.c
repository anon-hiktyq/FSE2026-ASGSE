
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo63()


            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (x >= 0) &&
(y >= 0) &&
(i >= 0) &&
(j >= 0)
    */
    
  
  while(unknown1())
  {
    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant x >= 0;
      loop invariant y >= 0;
      loop invariant i >= 0;
      loop invariant j >= 0;
    */
    
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