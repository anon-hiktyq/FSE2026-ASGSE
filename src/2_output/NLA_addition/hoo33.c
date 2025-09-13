
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
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((a@pre>b@pre) => (x >= 0 && x*u + y*v == a@pre*b@pre)) &&
((!(a@pre>b@pre)) => ((v == 0)&&(u == b@pre)&&(y == b@pre)&&(x == a@pre)&&(b == b@pre)&&(a == a@pre))) &&
(u == b@pre) &&
(y == b@pre) &&
(b == b@pre) &&
(a == a@pre
          loop assigns x, v)
    */
    
            while(x>y) {
      x=x-y;
      v=v+u;
    }
  
    //post-condition
    
  }