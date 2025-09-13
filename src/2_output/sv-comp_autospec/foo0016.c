
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0016(int n) 

            /*@
            Require n > 0
            Ensure Results(__return)
            */
            {
 
  int i = 0;
  int k = 0;
  
  
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (0 <= i && i <= n)) &&
((0 < n@pre) => (k == i)) &&
((!(0 < n@pre)) => ((k == 0)&&(i == 0)&&(n == n@pre))) &&
(n == n@pre
    loop assigns i, k)
    */
    
  while( i < n ) {
	  i++;
	  k++;
  }

  int j = 0;
 
 
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv
    ((0 < n@pre) => (0 <= j && j <= n)) &&
((0 < n@pre) => (k == n - j)) &&
((!(0 < n@pre)) => ((j == 0)&&(k == 0)&&(n == n@pre))) &&
(n == n@pre
    loop assigns j, k)
    */
    
  while( j < n ) {
    /*@ assert k > 0;*/
    j++;
    k--;
  }
}