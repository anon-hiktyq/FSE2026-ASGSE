
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo019(int n, int m) 

            /*@
            Require n >= 0 && m >= 0 && m < n
            Ensure Results(__return)
            */
            {
 
  int x = 0; 
  int y = m;
 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (0 <= x && x <= n)) &&
((0 < n@pre) => (y == m@pre + (x > m@pre ? (x - m@pre) : 0))) &&
((!(0 < n@pre)) => ((y == m@pre)&&(x == 0)&&(m == m@pre)&&(n == n@pre))) &&
(m == m@pre) &&
(n == n@pre
          loop assigns x, y)
    */
    
            while(x < n) {
    x++;
    if(x > m) y++;
  }
  
}