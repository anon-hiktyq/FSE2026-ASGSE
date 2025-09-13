
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void func18(int *a, int n) 
/*@
With a_l
Require store_int_array(a, n, a_l) && n > 0 && n < 100
Ensure emp
*/{
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  a_l,    
    store_int_array(a, n, a_l) && n > 0 && n < 100 &&
    (!(i < n@pre) => ((n == n@pre)&&(a == a@pre))) &&
(n == n@pre) &&
(a == a@pre) &&
(forall (j:Z), 0 <= j && j < i => (j % 2 == 0 => a_l[j] == 0)) &&
(forall (j:Z), 0 <= j && j < n => (j % 2 == 1 => a_l[j] == a_l[j]@pre)
          loop assigns a_l[0..n-1])
    */
    
            for (int i = 0; i < n; i++) {
        if (i%2==0) 
            a[i] = 0;
    }
}