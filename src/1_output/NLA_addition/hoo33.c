
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo33(int a, int b) 

            /*@
            Require a >= 1 && b >= 1
            Ensure Results(__return)
            */
            { 
    int x,y,u,v;
  
    //pre-condition
    x=a;
    y=b;
    u=b;
    v=0;
    
  
    //loop-body
    while(x>y) {
      x=x-y;
      v=v+u;
    }
  
    //post-condition
    
  }