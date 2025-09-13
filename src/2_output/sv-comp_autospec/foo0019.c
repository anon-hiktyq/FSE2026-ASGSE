
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0019(int n) 

            /*@
            Require n <= INT_MAX
            Ensure Results(__return)
            */
            {
  int i,k;
  k = n;
  i = 0;

  
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (((k == n@pre)&&(i == 0)&&(n == n@pre)) || (k + i/2 == n@pre))) &&
((0 < n@pre) => (0 <= i && i <= 2*n@pre && i % 2 == 0) ) &&
((0 < n@pre) => (k == n@pre - i/2) ) &&
((!(0 < n@pre)) => ((k == n@pre)&&(i == 0)&&(n == n@pre))) &&
(n == n@pre)
    */
    
            while( i < n ) {
    k--;
    i = i + 2;
  }

  int j = 0;

  
 
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv
    (k == n - i/2 - j) &&
(0 <= j && (n > 0 => j <= n/2))
    */
    
            while( j < n/2 ) {
    /*@ assert k > 0; */
    k--;
    j++;
  }
}