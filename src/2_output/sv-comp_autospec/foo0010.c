
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0010(int i, int j) 

            /*@
            Require 0 <= i && i < 1000000 && j >= 0
            Ensure Results(__return)
            */
            {

    int x = i;
    int y = j;
    int z = 0;
  
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((i@pre != 0) => (0 <= x && x <= i@pre)) &&
((i@pre != 0) => (y == j@pre - 2 * (i@pre - x))) &&
((i@pre != 0) => (z == i@pre - x)) &&
((!(i@pre != 0)) => ((z == 0)&&(y == j@pre)&&(x == i@pre)&&(j == j@pre)&&(i == i@pre))) &&
(j == j@pre) &&
(i == i@pre
          loop assigns x, y, z)
    */
    
            while (x != 0) {
        x--;
        y -= 2;
        z++;
    }

    if (i == j) {
        
    }
    
}