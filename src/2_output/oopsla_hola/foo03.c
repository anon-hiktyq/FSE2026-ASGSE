
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo03(int n, int l) 

            /*@
            Require l > 0 && n > l
            Ensure Results(__return)
            */
            {
  int i,k;

  k = 1;
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((!(1 < n@pre)) => ((k == 1) && (l == l@pre) && (n == n@pre))
              loop assigns k, i)
    */
    
            for (k = 1; k < n; k++) {
    i = l;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant l <= i <= n; // Modified invariant
      loop invariant i >= l;
      loop invariant i == l + (i - l);
    */
    for (; i < n; i++) {
    }
    
  }
    
  

}