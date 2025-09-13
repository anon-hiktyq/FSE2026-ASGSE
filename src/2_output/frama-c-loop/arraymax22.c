
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int arraymax22(int* a, int n) 
/*@
With a_l
Require store_int_array(a, n, a_l) && n > 0 && n < 100
Ensure Results(__return)
*/{
  int i = 1;
  int max = a[0];

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  a_l,    
    store_int_array(a, n, a_l) && n > 0 && n < 100 &&
    ((1 < n@pre) => (1 <= i && i <= n)) &&
((1 < n@pre) => (((max == a_l[0])&&(i == 1)&&(n == n@pre)&&(a == a@pre)) || (forall (j:Z), 0 <= j && j < i => a_l[j] <= max))) &&
((!(1 < n@pre)) => ((max == a_l[0])&&(i == 1)&&(n == n@pre)&&(a == a@pre))) &&
(n == n@pre) &&
(a == a@pre) &&
(forall (j:Z), 0 <= j && j < i => a_l[j] <= max
          loop assigns i, max)
    */
    
            while (i < n) {
    // Beginning of loop
    if (max < a[i])
    max = a[i];
    i = i + 1;
    // End of loop: Loop invariant comes here
  }
  return max;
}