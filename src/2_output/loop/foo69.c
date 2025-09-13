
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo69(int flag) 

            /*@
            Require flag > 0
            Ensure Results(__return)
            */
            {
  int i, j, k;
  j = 1;
  if (flag) {
    i = 0;
  } else {
    i = 1;
  }

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (i >= 0) &&
(j >= 1) &&
(flag == flag@pre
    loop assigns i, j
    loop variant i // i is strictly increasing, hence valid as a variant)
    */
    
  while (unknown1()) {
    i += 2;
    if (i % 2 == 0) {
      j += 2;
    } else {
      j++;
    }
  }

  int a = 0;
  int b = 0;

 
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv
    (a >= 0) &&
(b == a * (j - i)) &&
(flag == flag@pre
    loop assigns a, b
    loop variant a // a is strictly increasing, hence valid as a variant)
    */
    
  while (unknown2()) {
    a++;
    b += (j - i);
  }
  
}