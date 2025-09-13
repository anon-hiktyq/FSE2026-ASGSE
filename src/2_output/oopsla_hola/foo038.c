
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo038(int n) 

            /*@
            Require n > 0
            Ensure Results(__return)
            */
            {
  int x=0;
  int y=0;
  int i=0;
  
 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0<n@pre) => (x == i)) &&
((0<n@pre) => (y == (i / 2))) &&
((0<n@pre) => (0 <= i && i <= n@pre)) &&
(!(0<n@pre) => ((i == 0)&&(y == 0)&&(x == 0)&&(n == n@pre))) &&
(n == n@pre
    loop assigns i, x, y)
    */
    
  while(i<n) {
    i++;
    x++;
    if(i%2 == 0) y++;
  }
  
 
}