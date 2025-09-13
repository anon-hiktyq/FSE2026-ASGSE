
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo31(int A, int R) 

            /*@
            Require A >= 1 && (R-1)*(R-1) < A && A <= R*R && A%2 == 1
            Ensure Results(__return)
            */
            { 
    int u,v,r;
  
    //pre-condition
    u=2*R+1;
    v=1;
    r=R*R-A; 
  
    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (4*(A+r) == u*u-v*v-2*u+2*v
          loop assigns r, v)
    */
    
            while(r>0) {
      r=r-v;
      v=v+2;
    }
  
    //post-condition
    
  }