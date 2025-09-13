
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

  while (unknown1()) {
    i += 2;
    if (i % 2 == 0) {
      j += 2;
    } else j++;
  }

  int a = 0;
  int b = 0;

  while (unknown2()) {
    a++;
    b += (j - i);
  }
  
}