
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo029() 

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
(d >= 0
    loop assigns a, b, c, d, x, y)
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

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant a + c == b + d;
      loop invariant d >= 0;
    */
    while (unknown2()) {
      c--;
      b--;
    }
            
  }
  ;
}