
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo016(int i, int j) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  
  int x = i;
  int y = j;
 
 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((i != 0) => (x <= i@pre)) &&
((i != 0) => (y == j@pre - (i@pre - x))) &&
(!(i != 0) => (y == j@pre && x == i@pre && j == j@pre && i == i@pre)) &&
(j == j@pre) &&
(i == i@pre
    loop assigns x, y)
    */
    
  while(x != 0) {
    x--;
    y--;
  }

  
}