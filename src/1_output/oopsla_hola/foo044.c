
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo044(int k, int flag , int __BLAST_NONDET) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
  int i=0;
  int j=0;
  int n;
 

  if (flag == 1){
     n=1;
  } else {
     n=2;
  }

  i=0;
  
  while ( i <= k) {
    i++;
    j = j + n;
  }
  
    
	
}