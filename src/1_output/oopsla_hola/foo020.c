
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo020(int x, int y, int k, int j, int i, int n) 

            /*@
            Require x + y == k && n > 0
            Ensure Results(__return)
            */
            {
 
  int m = 0;
  j = 0;
  while (j < n) {
    if (j == i) {
      x++;
      y--;
    } else {
      y++;
      x--;
    }
    if (unknown()){
       m = j;
    }
    j++;
  }
  
  
  
  

}