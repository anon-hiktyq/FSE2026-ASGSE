
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int foo012(int flag)


            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (a == b) &&
(s == (a * (a + 1)) / 2
    loop assigns a, b, s, t)
    */
    
  while(unknown1()) {
    a++;
    b++;
    s += a;
    t += b;
    if(flag) {
      t += a;
    }
  } 
 
  int x = 1;

  if(flag) {
    x = t - 2*s + 2;
  }
  
  int y = 0;
  
 
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv
    (0 <= y // Weakened invariant for establishment
    loop assigns y)
    */
    
  while(y <= x){
    if(unknown2()) 
       y++;
    else 
       y += 2;
  }
  
}