
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo68(int n)


            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int x=0;
  int y=0;
  int i=0;
  
 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (x == i)) &&
((0 < n@pre) => (y == i / 2)) &&
((0 < n@pre) => (0 <= i && i <= n)) &&
((!(0 < n@pre)) => ((i == 0) && (y == 0) && (x == 0) && (n == n@pre))) &&
(n == n@pre
    loop assigns i, x, y
    loop variant n - i)
    */
    
  while(i < n) {
    i++;
    x++;
    if(i % 2 == 0) y++;
  }
  
 
}