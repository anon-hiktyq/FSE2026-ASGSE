
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0020(int n, int v) 

            /*@
            Require 0 <= n && n < 2 && 0 <= v
            Ensure Results(__return)
            */
            {
  int c1 = 4000;
  int c2 = 2000;
  int c3 = 10000;
  
  int i, k, j;

  k = 0;
  i = 0;

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (0 <= i && i <= n@pre)) &&
((0 < n@pre) => (k == i * (v == 0 ? c1 : (v == 1 ? c2 : c3)))) &&
((!(0 < n@pre)) => ((k == 0)&&(i == 0)&&(c3 == 10000)&&(c2 == 2000)&&(c1 == 4000)&&(v == v@pre)&&(n == n@pre))) &&
(c3 == 10000) &&
(c2 == 2000) &&
(c1 == 4000) &&
(v == v@pre) &&
(n == n@pre
            loop assigns i, k)
    */
    
            while (i < n) {
    i++;
    if (v == 0)
      k += c1;
    else if (v == 1)
      k += c2;
    else
      k += c3;
  }

  j = 0;

 
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv
    ((0 <= j && j <= n)) &&
(k == (v == 0 ? c1 : (v == 1 ? c2 : c3)) * i - j // Corrected line) &&
(n == n@pre
            loop assigns j, k)
    */
    
            while (j < n) {
    /*@ assert k > 0; */
    j++;
    k--;
  }

}