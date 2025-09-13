
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo09(int pvlen) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  
  int t;
  int k = 0;
  int n;
  int i = 0;

 
  while (unknown1()){
    i = i + 1;
  
  if (i > pvlen) {
    pvlen = i;
  } else {

  }
}
  i = 0;

 
  while (unknown2()) {
    t = i;
    i = i + 1;
    k = k + 1;
  }
  while (unknown3()){
      ;
  }

  int j = 0;
  n = i;
  
  while (1) {
    
    k = k - 1;
    i = i - 1;
    j = j + 1;
    if (j < n) {
    } else {
      break;
    }
    
  }
}