
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo021(int n,int j,int v) 

            /*@
            Require n > 0 && n < 10
            Ensure Results(__return)
            */
            {
  int c1 = 4000;
  int c2 = 2000;
  int i = 0;
  int k = 0;
 
  while( i < n ) {
    i++;
    if(unknown() % 2 == 0) {
        v = 0;
    }
    else v = 1;
    
    if( v == 0 ){
      k += c1;
    }else {
      k += c2;
    }
  }
  
  
}