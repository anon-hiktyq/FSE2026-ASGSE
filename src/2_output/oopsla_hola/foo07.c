
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo07(int n) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {

  int i, a, b;
  i = 0; a = 0; b = 0;
  
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (0 <= i && i <= n)) &&
((0 < n@pre) => (a + b == 3 * i)) &&
((0 < n@pre) => (a >= 0 && b >= 0)) &&
((!(0 < n@pre)) => ((b == 0)&&(a == 0)&&(i == 0)&&(n == n@pre))) &&
(n == n@pre
          loop assigns a, b, i)
    */
    
            while( i < n ) {
    if(unknown()) {
      a = a + 1;
      b = b + 2;
    } else {
      a = a + 2;
      b = b + 1;
    }
    i = i + 1;
  }
  
}