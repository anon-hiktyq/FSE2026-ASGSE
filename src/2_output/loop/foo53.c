
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo53(int n, int l) 

            /*@
            Require l > 0 && n > l
            Ensure Results(__return)
            */
            {
  int i,k;

  k = 1;
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((1 < n@pre) => (forall (i:Z), (l <= i && i < n) => (1 <= i))) &&
((1 < n@pre) => (1 <= k && k <= n + 1)) &&
((!(1 < n@pre)) => ((k == 1) && (l == l@pre) && (n == n@pre)))
    */
    
  for (k = 1; k < n; k++) {
    i = l;

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant l > 0;
      loop invariant 1 <= k <= n;
    */
    for (i = l; i < n; i++) {
    }
  }
  
    
  

}