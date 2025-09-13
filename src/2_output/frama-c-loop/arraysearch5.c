
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int arraysearch5(int* a, int x, int n) 
/*@
With a_l
Require store_int_array(a, x, a_l) && x > 0 && x < 100
Ensure Results(__return)
*/{ 

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  a_l,    
    store_int_array(a, x, a_l) && x > 0 && x < 100 &&
    ((!(p < n@pre)) => ((n == n@pre)&&(x == x@pre)&&(a == a@pre))) &&
(n == n@pre) &&
(x == x@pre) &&
(a == a@pre) &&
(forall (i:Z), 0 <= i && i < p => a_l[i] == a_l[i]@pre
          loop assigns p)
    */
    
            for (int p = 0; p < n; p++) {
    // STart
    if (x == a[p]) 
       return 1;
    // End
  }
  return 0;
}