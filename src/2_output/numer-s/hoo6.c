
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int hoo6(int a,int w,int x,int y,int z) 

            /*@
            Require x > 0 && y > 0 && z > 0 && w > 0
            Ensure Results(__return)
            */
            {

    //pre-condition
    x = w;
    z = x + 1;
    y = w + 1;


    //loop-body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while (unknown()) {
        y = y + 1;
        z = z + 1;
    }

    //post-conditon
    
}