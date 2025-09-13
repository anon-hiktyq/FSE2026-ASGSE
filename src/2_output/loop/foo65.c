
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo65() 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int a = 1;
  int b = 1;
  int c = 2;
  int d = 2;
  int x = 3;
  int y = 3;
 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (a + c == b + d) &&
(((y == 3) && (x == 3) && (d == 2) && (c == 2) && (b == 1) && (a == 1)) || (a + c == b + d))
    */
    
  while (unknown1()) {
    x = a + c;
    y = b + d;

    if ((x + y) % 2 == 0) {
      a++;
      d++;
    } else {
      a--;
    }

    /*@
      loop invariant a + c == b + d;
    */
    while (unknown2()) {
      c--;
      b--;
    }
  }
  
}